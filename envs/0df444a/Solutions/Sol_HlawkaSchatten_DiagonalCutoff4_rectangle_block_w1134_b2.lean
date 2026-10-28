-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1134_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:29:00.808347+00:00
-- url     : https://prove2.me/submissions/5031e82e-3faa-4dcb-b9f3-9803f97f9036

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
theorem support_rectangle_w1134_s6_0 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1085344501/5000000000 : ℝ)*x 0 + (5393539651/10000000000 : ℝ)*x 1 + (1053053271/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085344501/5000000000 : ℝ)^8327 ≤ (1648647939529/12500000000000 : ℝ)^6279 := by
    have hnat : (1085344501 : ℕ)^8327*12500000000000^6279 ≤ 1648647939529^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085344501 5000000000 1648647939529 12500000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393539651/10000000000 : ℝ)^8327 ≤ (2756132614737/6250000000000 : ℝ)^6279 := by
    have hnat : (5393539651 : ℕ)^8327*6250000000000^6279 ≤ 2756132614737^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393539651 10000000000 2756132614737 6250000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053053271/2000000000 : ℝ)^8327 ≤ (8542538926321/20000000000000 : ℝ)^6279 := by
    have hnat : (1053053271 : ℕ)^8327*20000000000000^6279 ≤ 8542538926321^6279*2000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053053271 2000000000 8542538926321 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1085344501/5000000000 : ℝ), (5393539651/10000000000 : ℝ), (1053053271/2000000000 : ℝ)] ![(1648647939529/12500000000000 : ℝ), (2756132614737/6250000000000 : ℝ), (8542538926321/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1085344501/5000000000 : ℝ)|^8327 ≤ (1648647939529/12500000000000 : ℝ)^6279
        have hw : |(-1085344501/5000000000 : ℝ)|=(1085344501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393539651/10000000000 : ℝ)|^8327 ≤ (2756132614737/6250000000000 : ℝ)^6279
        have hw : |(5393539651/10000000000 : ℝ)|=(5393539651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053053271/2000000000 : ℝ)|^8327 ≤ (8542538926321/20000000000000 : ℝ)^6279
        have hw : |(1053053271/2000000000 : ℝ)|=(1053053271/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s6_1 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068975387/2000000000 : ℝ)*x 0 + (-111787927/500000000 : ℝ)*x 1 + (2632633169/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068975387/2000000000 : ℝ)^8327 ≤ (43571256230313/100000000000000 : ℝ)^6279 := by
    have hnat : (1068975387 : ℕ)^8327*100000000000000^6279 ≤ 43571256230313^6279*2000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068975387 2000000000 43571256230313 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (111787927/500000000 : ℝ)^8327 ≤ (6858024655469/50000000000000 : ℝ)^6279 := by
    have hnat : (111787927 : ℕ)^8327*50000000000000^6279 ≤ 6858024655469^6279*500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111787927 500000000 6858024655469 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632633169/5000000000 : ℝ)^8327 ≤ (42712694448717/100000000000000 : ℝ)^6279 := by
    have hnat : (2632633169 : ℕ)^8327*100000000000000^6279 ≤ 42712694448717^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632633169 5000000000 42712694448717 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068975387/2000000000 : ℝ), (-111787927/500000000 : ℝ), (2632633169/5000000000 : ℝ)] ![(43571256230313/100000000000000 : ℝ), (6858024655469/50000000000000 : ℝ), (42712694448717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068975387/2000000000 : ℝ)|^8327 ≤ (43571256230313/100000000000000 : ℝ)^6279
        have hw : |(1068975387/2000000000 : ℝ)|=(1068975387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-111787927/500000000 : ℝ)|^8327 ≤ (6858024655469/50000000000000 : ℝ)^6279
        have hw : |(-111787927/500000000 : ℝ)|=(111787927/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632633169/5000000000 : ℝ)|^8327 ≤ (42712694448717/100000000000000 : ℝ)^6279
        have hw : |(2632633169/5000000000 : ℝ)|=(2632633169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s6_2 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068975383/2000000000 : ℝ)*x 0 + (131631659/250000000 : ℝ)*x 1 + (-1117879269/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068975383/2000000000 : ℝ)^8327 ≤ (2723203500881/6250000000000 : ℝ)^6279 := by
    have hnat : (1068975383 : ℕ)^8327*6250000000000^6279 ≤ 2723203500881^6279*2000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068975383 2000000000 2723203500881 6250000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131631659/250000000 : ℝ)^8327 ≤ (8542538937079/20000000000000 : ℝ)^6279 := by
    have hnat : (131631659 : ℕ)^8327*20000000000000^6279 ≤ 8542538937079^6279*250000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131631659 250000000 8542538937079 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1117879269/5000000000 : ℝ)^8327 ≤ (6858024647333/50000000000000 : ℝ)^6279 := by
    have hnat : (1117879269 : ℕ)^8327*50000000000000^6279 ≤ 6858024647333^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117879269 5000000000 6858024647333 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068975383/2000000000 : ℝ), (131631659/250000000 : ℝ), (-1117879269/5000000000 : ℝ)] ![(2723203500881/6250000000000 : ℝ), (8542538937079/20000000000000 : ℝ), (6858024647333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068975383/2000000000 : ℝ)|^8327 ≤ (2723203500881/6250000000000 : ℝ)^6279
        have hw : |(1068975383/2000000000 : ℝ)|=(1068975383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131631659/250000000 : ℝ)|^8327 ≤ (8542538937079/20000000000000 : ℝ)^6279
        have hw : |(131631659/250000000 : ℝ)|=(131631659/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1117879269/5000000000 : ℝ)|^8327 ≤ (6858024647333/50000000000000 : ℝ)^6279
        have hw : |(-1117879269/5000000000 : ℝ)|=(1117879269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s6_3 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4365783417/10000000000 : ℝ)*x 0 + (530029811/1250000000 : ℝ)*x 1 + (4495034567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365783417/10000000000 : ℝ)^8327 ≤ (2082296246199/6250000000000 : ℝ)^6279 := by
    have hnat : (4365783417 : ℕ)^8327*6250000000000^6279 ≤ 2082296246199^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365783417 10000000000 2082296246199 6250000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (530029811/1250000000 : ℝ)^8327 ≤ (32052170500633/100000000000000 : ℝ)^6279 := by
    have hnat : (530029811 : ℕ)^8327*100000000000000^6279 ≤ 32052170500633^6279*1250000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530029811 1250000000 32052170500633 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4495034567/10000000000 : ℝ)^8327 ≤ (6926217909343/20000000000000 : ℝ)^6279 := by
    have hnat : (4495034567 : ℕ)^8327*20000000000000^6279 ≤ 6926217909343^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495034567 10000000000 6926217909343 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365783417/10000000000 : ℝ), (530029811/1250000000 : ℝ), (4495034567/10000000000 : ℝ)] ![(2082296246199/6250000000000 : ℝ), (32052170500633/100000000000000 : ℝ), (6926217909343/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365783417/10000000000 : ℝ)|^8327 ≤ (2082296246199/6250000000000 : ℝ)^6279
        have hw : |(4365783417/10000000000 : ℝ)|=(4365783417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(530029811/1250000000 : ℝ)|^8327 ≤ (32052170500633/100000000000000 : ℝ)^6279
        have hw : |(530029811/1250000000 : ℝ)|=(530029811/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4495034567/10000000000 : ℝ)|^8327 ≤ (6926217909343/20000000000000 : ℝ)^6279
        have hw : |(4495034567/10000000000 : ℝ)|=(4495034567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s6_4 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2170694079/10000000000 : ℝ)*x 0 + (2632795121/5000000000 : ℝ)*x 1 + (5393214517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170694079/10000000000 : ℝ)^8327 ≤ (13189224425877/100000000000000 : ℝ)^6279 := by
    have hnat : (2170694079 : ℕ)^8327*100000000000000^6279 ≤ 13189224425877^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170694079 10000000000 13189224425877 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632795121/5000000000 : ℝ)^8327 ≤ (5339522383539/12500000000000 : ℝ)^6279 := by
    have hnat : (2632795121 : ℕ)^8327*12500000000000^6279 ≤ 5339522383539^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632795121 5000000000 5339522383539 12500000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393214517/10000000000 : ℝ)^8327 ≤ (44094596484367/100000000000000 : ℝ)^6279 := by
    have hnat : (5393214517 : ℕ)^8327*100000000000000^6279 ≤ 44094596484367^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393214517 10000000000 44094596484367 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2170694079/10000000000 : ℝ), (2632795121/5000000000 : ℝ), (5393214517/10000000000 : ℝ)] ![(13189224425877/100000000000000 : ℝ), (5339522383539/12500000000000 : ℝ), (44094596484367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2170694079/10000000000 : ℝ)|^8327 ≤ (13189224425877/100000000000000 : ℝ)^6279
        have hw : |(-2170694079/10000000000 : ℝ)|=(2170694079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632795121/5000000000 : ℝ)|^8327 ≤ (5339522383539/12500000000000 : ℝ)^6279
        have hw : |(2632795121/5000000000 : ℝ)|=(2632795121/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393214517/10000000000 : ℝ)|^8327 ≤ (44094596484367/100000000000000 : ℝ)^6279
        have hw : |(5393214517/10000000000 : ℝ)|=(5393214517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s6_5 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656198839/5000000000 : ℝ)*x 0 + (-2107810399/10000000000 : ℝ)*x 1 + (5393214547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656198839/5000000000 : ℝ)^8327 ≤ (5402559476079/12500000000000 : ℝ)^6279 := by
    have hnat : (2656198839 : ℕ)^8327*12500000000000^6279 ≤ 5402559476079^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656198839 5000000000 5402559476079 12500000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2107810399/10000000000 : ℝ)^8327 ≤ (1268492736771/10000000000000 : ℝ)^6279 := by
    have hnat : (2107810399 : ℕ)^8327*10000000000000^6279 ≤ 1268492736771^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107810399 10000000000 1268492736771 10000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393214547/10000000000 : ℝ)^8327 ≤ (22047298404823/50000000000000 : ℝ)^6279 := by
    have hnat : (5393214547 : ℕ)^8327*50000000000000^6279 ≤ 22047298404823^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393214547 10000000000 22047298404823 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656198839/5000000000 : ℝ), (-2107810399/10000000000 : ℝ), (5393214547/10000000000 : ℝ)] ![(5402559476079/12500000000000 : ℝ), (1268492736771/10000000000000 : ℝ), (22047298404823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656198839/5000000000 : ℝ)|^8327 ≤ (5402559476079/12500000000000 : ℝ)^6279
        have hw : |(2656198839/5000000000 : ℝ)|=(2656198839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2107810399/10000000000 : ℝ)|^8327 ≤ (1268492736771/10000000000000 : ℝ)^6279
        have hw : |(-2107810399/10000000000 : ℝ)|=(2107810399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393214547/10000000000 : ℝ)|^8327 ≤ (22047298404823/50000000000000 : ℝ)^6279
        have hw : |(5393214547/10000000000 : ℝ)|=(5393214547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s6_6 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656198881/5000000000 : ℝ)*x 0 + (5393214351/10000000000 : ℝ)*x 1 + (-263476319/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656198881/5000000000 : ℝ)^8327 ≤ (43220476714941/100000000000000 : ℝ)^6279 := by
    have hnat : (2656198881 : ℕ)^8327*100000000000000^6279 ≤ 43220476714941^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656198881 5000000000 43220476714941 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393214351/10000000000 : ℝ)^8327 ≤ (8818918936897/20000000000000 : ℝ)^6279 := by
    have hnat : (5393214351 : ℕ)^8327*20000000000000^6279 ≤ 8818918936897^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393214351 10000000000 8818918936897 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263476319/1250000000 : ℝ)^8327 ≤ (2536985717759/20000000000000 : ℝ)^6279 := by
    have hnat : (263476319 : ℕ)^8327*20000000000000^6279 ≤ 2536985717759^6279*1250000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263476319 1250000000 2536985717759 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656198881/5000000000 : ℝ), (5393214351/10000000000 : ℝ), (-263476319/1250000000 : ℝ)] ![(43220476714941/100000000000000 : ℝ), (8818918936897/20000000000000 : ℝ), (2536985717759/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656198881/5000000000 : ℝ)|^8327 ≤ (43220476714941/100000000000000 : ℝ)^6279
        have hw : |(2656198881/5000000000 : ℝ)|=(2656198881/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393214351/10000000000 : ℝ)|^8327 ≤ (8818918936897/20000000000000 : ℝ)^6279
        have hw : |(5393214351/10000000000 : ℝ)|=(5393214351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-263476319/1250000000 : ℝ)|^8327 ≤ (2536985717759/20000000000000 : ℝ)^6279
        have hw : |(-263476319/1250000000 : ℝ)|=(263476319/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s6_7 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2182896647/5000000000 : ℝ)*x 0 + (898878217/2000000000 : ℝ)*x 1 + (1060221083/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182896647/5000000000 : ℝ)^8327 ≤ (2082302493661/6250000000000 : ℝ)^6279 := by
    have hnat : (2182896647 : ℕ)^8327*6250000000000^6279 ≤ 2082302493661^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182896647 5000000000 2082302493661 6250000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (898878217/2000000000 : ℝ)^8327 ≤ (1731225756321/5000000000000 : ℝ)^6279 := by
    have hnat : (898878217 : ℕ)^8327*5000000000000^6279 ≤ 1731225756321^6279*2000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898878217 2000000000 1731225756321 5000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1060221083/2500000000 : ℝ)^8327 ≤ (16029322481111/50000000000000 : ℝ)^6279 := by
    have hnat : (1060221083 : ℕ)^8327*50000000000000^6279 ≤ 16029322481111^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060221083 2500000000 16029322481111 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182896647/5000000000 : ℝ), (898878217/2000000000 : ℝ), (1060221083/2500000000 : ℝ)] ![(2082302493661/6250000000000 : ℝ), (1731225756321/5000000000000 : ℝ), (16029322481111/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182896647/5000000000 : ℝ)|^8327 ≤ (2082302493661/6250000000000 : ℝ)^6279
        have hw : |(2182896647/5000000000 : ℝ)|=(2182896647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(898878217/2000000000 : ℝ)|^8327 ≤ (1731225756321/5000000000000 : ℝ)^6279
        have hw : |(898878217/2000000000 : ℝ)|=(898878217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1060221083/2500000000 : ℝ)|^8327 ≤ (16029322481111/50000000000000 : ℝ)^6279
        have hw : |(1060221083/2500000000 : ℝ)|=(1060221083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1134_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11303/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2267/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3513/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2817/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11303/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2817/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11303/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2817/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11303/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2817/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11303/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2817/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11303/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2817/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11303/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11303/100000 : ℝ) ^ (4163/1024 : ℝ) ≤ (14152255868239699/100000000000000000000 : ℝ) := by
    have hpowers : (11303/100000 : ℝ)^4163 ≤ (14152255868239699/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11303 : ℕ)^4163*100000000000000000000^1024 ≤ 14152255868239699^1024*100000^4163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11303 100000 14152255868239699 100000000000000000000 4163 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11303/100000 : ℝ)) (X := (14152255868239699/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2817/20000 : ℝ) ^ (4163/1024 : ℝ) ≤ (6924060082519691/20000000000000000000 : ℝ) := by
    have hpowers : (2817/20000 : ℝ)^4163 ≤ (6924060082519691/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2817 : ℕ)^4163*20000000000000000000^1024 ≤ 6924060082519691^1024*20000^4163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2817 20000 6924060082519691 20000000000000000000 4163 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2817/20000 : ℝ)) (X := (6924060082519691/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014152255868239699/50000000000000000000 : ℝ) ≤ (10000696150075129/10000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (50014152255868239699/50000000000000000000 : ℝ)^1024 ≤ (10000696150075129/10000000000000000 : ℝ)^4163 := by
      have hnat : (50014152255868239699 : ℕ)^1024*10000000000000000^4163 ≤ 10000696150075129^4163*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014152255868239699 50000000000000000000 10000696150075129 10000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000696150075129/10000000000000000 : ℝ)) (X := (50014152255868239699/50000000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024386278140419077/50000000000000000000 : ℝ) ≤ (10001199469536361/10000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (50024386278140419077/50000000000000000000 : ℝ)^1024 ≤ (10001199469536361/10000000000000000 : ℝ)^4163 := by
      have hnat : (50024386278140419077 : ℕ)^1024*10000000000000000^4163 ≤ 10001199469536361^4163*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024386278140419077 50000000000000000000 10001199469536361 10000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001199469536361/10000000000000000 : ℝ)) (X := (50024386278140419077/50000000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006924060082519691/10000000000000000000 : ℝ) ≤ (10001702788997593/10000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (10006924060082519691/10000000000000000000 : ℝ)^1024 ≤ (10001702788997593/10000000000000000 : ℝ)^4163 := by
      have hnat : (10006924060082519691 : ℕ)^1024*10000000000000000^4163 ≤ 10001702788997593^4163*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006924060082519691 10000000000000000000 10001702788997593 10000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001702788997593/10000000000000000 : ℝ)) (X := (10006924060082519691/10000000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14152255868239699/100000000000000000000 : ℝ) ≤ ((13905279324884199143/13910000000000000000 : ℝ)+2*(31457466327/17387500000000 : ℝ)*(11303/100000 : ℝ))^(4163/1024 : ℝ) := by
    rw [show (13905279324884199143/13910000000000000000 : ℝ)+2*(31457466327/17387500000000 : ℝ)*(11303/100000 : ℝ)=(10000696150075129/10000000000000000 : ℝ) by norm_num, show 1+2*(14152255868239699/100000000000000000000 : ℝ)=(50014152255868239699/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6924060082519691/20000000000000000000 : ℝ)+(14152255868239699/100000000000000000000 : ℝ) ≤ ((13905279324884199143/13910000000000000000 : ℝ)+(31457466327/17387500000000 : ℝ)*((2817/20000 : ℝ)+(11303/100000 : ℝ)))^(4163/1024 : ℝ) := by
    rw [show (13905279324884199143/13910000000000000000 : ℝ)+(31457466327/17387500000000 : ℝ)*((2817/20000 : ℝ)+(11303/100000 : ℝ))=(10001199469536361/10000000000000000 : ℝ) by norm_num, show 1+(6924060082519691/20000000000000000000 : ℝ)+(14152255868239699/100000000000000000000 : ℝ)=(50024386278140419077/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6924060082519691/20000000000000000000 : ℝ) ≤ ((13905279324884199143/13910000000000000000 : ℝ)+2*(31457466327/17387500000000 : ℝ)*(2817/20000 : ℝ))^(4163/1024 : ℝ) := by
    rw [show (13905279324884199143/13910000000000000000 : ℝ)+2*(31457466327/17387500000000 : ℝ)*(2817/20000 : ℝ)=(10001702788997593/10000000000000000 : ℝ) by norm_num, show 1+2*(6924060082519691/20000000000000000000 : ℝ)=(10006924060082519691/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13905279324884199143/13910000000000000000 : ℝ)*(X 1 0+X 2 0)+(31457466327/17387500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (11303/100000 : ℝ)) (hi := (2817/20000 : ℝ)) (c := (13905279324884199143/13910000000000000000 : ℝ)) (alpha := (31457466327/17387500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13905279324884199143/13910000000000000000 : ℝ)*(X 0 1+X 2 1)+(31457466327/17387500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (11303/100000 : ℝ)) (hi := (2817/20000 : ℝ)) (c := (13905279324884199143/13910000000000000000 : ℝ)) (alpha := (31457466327/17387500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13905279324884199143/13910000000000000000 : ℝ)*(X 0 2+X 1 2)+(31457466327/17387500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (11303/100000 : ℝ)) (hi := (2817/20000 : ℝ)) (c := (13905279324884199143/13910000000000000000 : ℝ)) (alpha := (31457466327/17387500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1085344501/5000000000 : ℝ)*X 0 0+(5393539651/10000000000 : ℝ)*X 0 1+(1053053271/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068975387/2000000000 : ℝ)*X 1 0+(-111787927/500000000 : ℝ)*X 1 1+(2632633169/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068975383/2000000000 : ℝ)*X 2 0+(131631659/250000000 : ℝ)*X 2 1+(-1117879269/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4365783417/10000000000 : ℝ)*X 0 0+(530029811/1250000000 : ℝ)*X 0 1+(4495034567/10000000000 : ℝ)*X 0 2+(4365783417/10000000000 : ℝ)*X 1 0+(530029811/1250000000 : ℝ)*X 1 1+(4495034567/10000000000 : ℝ)*X 1 2+(4365783417/10000000000 : ℝ)*X 2 0+(530029811/1250000000 : ℝ)*X 2 1+(4495034567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2170694079/10000000000 : ℝ)*X 0 0+(2632795121/5000000000 : ℝ)*X 0 1+(5393214517/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656198839/5000000000 : ℝ)*X 1 0+(-2107810399/10000000000 : ℝ)*X 1 1+(5393214547/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656198881/5000000000 : ℝ)*X 2 0+(5393214351/10000000000 : ℝ)*X 2 1+(-263476319/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2182896647/5000000000 : ℝ)*X 0 0+(898878217/2000000000 : ℝ)*X 0 1+(1060221083/2500000000 : ℝ)*X 0 2+(2182896647/5000000000 : ℝ)*X 1 0+(898878217/2000000000 : ℝ)*X 1 1+(1060221083/2500000000 : ℝ)*X 1 2+(2182896647/5000000000 : ℝ)*X 2 0+(898878217/2000000000 : ℝ)*X 2 1+(1060221083/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5602960614333102453774681357/695500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1808012667/100000000000000 : ℝ)*(base19) + (101825041/6250000000000 : ℝ)*(base23) + (79980909/100000000000000 : ℝ)*(lower2) + (216267183/100000000000000 : ℝ)*(upper3) + (25873163/25000000000000 : ℝ)*(upper5) + (5860357723087833/100000000000000 : ℝ)*(major0) + (5860357723087833/100000000000000 : ℝ)*(major1) + (5860357723087833/100000000000000 : ℝ)*(major2) + (3897953561685221/50000000000000 : ℝ)*(sp0) + (389797714124799/5000000000000 : ℝ)*(sp1) + (779595446130799/10000000000000 : ℝ)*(sp2) + (490591450445039/12500000000000 : ℝ)*(sp3) + (12241784551/25000000000000 : ℝ)*(sp4) + (27483572763/100000000000000 : ℝ)*(sp7) + (156990363485323/4000000000000 : ℝ)*(f.failure) + (3897978045254323/50000000000000 : ℝ)*(f.sum) + (14844632156149/3477500000000000000000000000 : ℝ)*base65 + (18382168839645872881/1391000000000000000000000000000000 : ℝ)*base68 + (9010747732947127119/1391000000000000000000000000000000 : ℝ)*base69 + (9971263656899127119/1391000000000000000000000000000000 : ℝ)*base71 + (19879845479123/6955000000000000000000000000 : ℝ)*base73 + (27005211860094872881/1391000000000000000000000000000000 : ℝ)*base76 + (2163583247150872881/1391000000000000000000000000000000 : ℝ)*base78 + (1704100108035872881/1391000000000000000000000000000000 : ℝ)*base80 + (3823123824641/869375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (15817/200000000000000000000 : ℝ)*base90 + (15817/200000000000000000000 : ℝ)*base92 + (15817/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (432436523728679575819653969/139100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (758297347/100000000000000 : ℝ)*(base19) + (451318899/50000000000000 : ℝ)*(base23) + (37643437/100000000000000 : ℝ)*(upper2) + (75347461/100000000000000 : ℝ)*(upper3) + (54648681/50000000000000 : ℝ)*(upper5) + (1178016865424913/20000000000000 : ℝ)*(major0) + (1178016865424913/20000000000000 : ℝ)*(major1) + (1178016865424913/20000000000000 : ℝ)*(major2) + (5812710529/25000000000000 : ℝ)*(sp1) + (15004934979/100000000000000 : ℝ)*(sp2) + (1567100232709217/20000000000000 : ℝ)*(sp4) + (244858661075207/3125000000000 : ℝ)*(sp5) + (1958871313993327/25000000000000 : ℝ)*(sp6) + (1972333693537889/50000000000000 : ℝ)*(sp7) + (1972333693537889/50000000000000 : ℝ)*(f.failure) + (1567100232709217/20000000000000 : ℝ)*(f.sum) + (1924205669239/1391000000000000000000000000 : ℝ)*base66 + (3749000209106249559/278200000000000000000000000000000 : ℝ)*base67 + (7549912009800049559/278200000000000000000000000000000 : ℝ)*base69 + (2780946399401449559/278200000000000000000000000000000 : ℝ)*base71 + (1360751956783/695500000000000000000000000 : ℝ)*base74 + (2982720806583849559/278200000000000000000000000000000 : ℝ)*base75 + (849227712989649559/278200000000000000000000000000000 : ℝ)*base77 + (9090093299826649559/278200000000000000000000000000000 : ℝ)*base79 + (3378320059/139100000000000000000000000 : ℝ)*base82 + (1/50000000000000 : ℝ)*base85 + (13431131/2500000000000000000000 : ℝ)*base90 + (13431131/2500000000000000000000 : ℝ)*base92 + (13431131/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1134_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11303/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2267/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1134_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1134_s7_0 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1085358169/5000000000 : ℝ)*x 0 + (5393206629/10000000000 : ℝ)*x 1 + (5265581521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085358169/5000000000 : ℝ)^8327 ≤ (1318940378567/10000000000000 : ℝ)^6279 := by
    have hnat : (1085358169 : ℕ)^8327*10000000000000^6279 ≤ 1318940378567^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085358169 5000000000 1318940378567 10000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393206629/10000000000 : ℝ)^8327 ≤ (44094510957501/100000000000000 : ℝ)^6279 := by
    have hnat : (5393206629 : ℕ)^8327*100000000000000^6279 ≤ 44094510957501^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393206629 10000000000 44094510957501 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265581521/10000000000 : ℝ)^8327 ≤ (42716085245253/100000000000000 : ℝ)^6279 := by
    have hnat : (5265581521 : ℕ)^8327*100000000000000^6279 ≤ 42716085245253^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265581521 10000000000 42716085245253 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1085358169/5000000000 : ℝ), (5393206629/10000000000 : ℝ), (5265581521/10000000000 : ℝ)] ![(1318940378567/10000000000000 : ℝ), (44094510957501/100000000000000 : ℝ), (42716085245253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1085358169/5000000000 : ℝ)|^8327 ≤ (1318940378567/10000000000000 : ℝ)^6279
        have hw : |(-1085358169/5000000000 : ℝ)|=(1085358169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393206629/10000000000 : ℝ)|^8327 ≤ (44094510957501/100000000000000 : ℝ)^6279
        have hw : |(5393206629/10000000000 : ℝ)|=(5393206629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265581521/10000000000 : ℝ)|^8327 ≤ (42716085245253/100000000000000 : ℝ)^6279
        have hw : |(5265581521/10000000000 : ℝ)|=(5265581521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s7_1 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334049603/625000000 : ℝ)*x 0 + (-2235452417/10000000000 : ℝ)*x 1 + (5265581531/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334049603/625000000 : ℝ)^8327 ≤ (4357035582807/10000000000000 : ℝ)^6279 := by
    have hnat : (334049603 : ℕ)^8327*10000000000000^6279 ≤ 4357035582807^6279*625000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334049603 625000000 4357035582807 10000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2235452417/10000000000 : ℝ)^8327 ≤ (6856779399913/50000000000000 : ℝ)^6279 := by
    have hnat : (2235452417 : ℕ)^8327*50000000000000^6279 ≤ 6856779399913^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2235452417 10000000000 6856779399913 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265581531/10000000000 : ℝ)^8327 ≤ (8543217070567/20000000000000 : ℝ)^6279 := by
    have hnat : (5265581531 : ℕ)^8327*20000000000000^6279 ≤ 8543217070567^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265581531 10000000000 8543217070567 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334049603/625000000 : ℝ), (-2235452417/10000000000 : ℝ), (5265581531/10000000000 : ℝ)] ![(4357035582807/10000000000000 : ℝ), (6856779399913/50000000000000 : ℝ), (8543217070567/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334049603/625000000 : ℝ)|^8327 ≤ (4357035582807/10000000000000 : ℝ)^6279
        have hw : |(334049603/625000000 : ℝ)|=(334049603/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2235452417/10000000000 : ℝ)|^8327 ≤ (6856779399913/50000000000000 : ℝ)^6279
        have hw : |(-2235452417/10000000000 : ℝ)|=(2235452417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265581531/10000000000 : ℝ)|^8327 ≤ (8543217070567/20000000000000 : ℝ)^6279
        have hw : |(5265581531/10000000000 : ℝ)|=(5265581531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s7_2 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336198413/2500000000 : ℝ)*x 0 + (2632790767/5000000000 : ℝ)*x 1 + (-2235452409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336198413/2500000000 : ℝ)^8327 ≤ (43570355871313/100000000000000 : ℝ)^6279 := by
    have hnat : (1336198413 : ℕ)^8327*100000000000000^6279 ≤ 43570355871313^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336198413 2500000000 43570355871313 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632790767/5000000000 : ℝ)^8327 ≤ (4271608538511/10000000000000 : ℝ)^6279 := by
    have hnat : (2632790767 : ℕ)^8327*10000000000000^6279 ≤ 4271608538511^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632790767 5000000000 4271608538511 10000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2235452409/10000000000 : ℝ)^8327 ≤ (6856779367371/50000000000000 : ℝ)^6279 := by
    have hnat : (2235452409 : ℕ)^8327*50000000000000^6279 ≤ 6856779367371^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2235452409 10000000000 6856779367371 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336198413/2500000000 : ℝ), (2632790767/5000000000 : ℝ), (-2235452409/10000000000 : ℝ)] ![(43570355871313/100000000000000 : ℝ), (4271608538511/10000000000000 : ℝ), (6856779367371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336198413/2500000000 : ℝ)|^8327 ≤ (43570355871313/100000000000000 : ℝ)^6279
        have hw : |(1336198413/2500000000 : ℝ)|=(1336198413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632790767/5000000000 : ℝ)|^8327 ≤ (4271608538511/10000000000000 : ℝ)^6279
        have hw : |(2632790767/5000000000 : ℝ)|=(2632790767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2235452409/10000000000 : ℝ)|^8327 ≤ (6856779367371/50000000000000 : ℝ)^6279
        have hw : |(-2235452409/10000000000 : ℝ)|=(2235452409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s7_3 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4365799919/10000000000 : ℝ)*x 0 + (4240880173/10000000000 : ℝ)*x 1 + (4494388603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365799919/10000000000 : ℝ)^8327 ≤ (33316906946403/100000000000000 : ℝ)^6279 := by
    have hnat : (4365799919 : ℕ)^8327*100000000000000^6279 ≤ 33316906946403^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365799919 10000000000 33316906946403 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4240880173/10000000000 : ℝ)^8327 ≤ (1602930163401/5000000000000 : ℝ)^6279 := by
    have hnat : (4240880173 : ℕ)^8327*5000000000000^6279 ≤ 1602930163401^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240880173 10000000000 1602930163401 5000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4494388603/10000000000 : ℝ)^8327 ≤ (8656122442139/25000000000000 : ℝ)^6279 := by
    have hnat : (4494388603 : ℕ)^8327*25000000000000^6279 ≤ 8656122442139^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494388603 10000000000 8656122442139 25000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365799919/10000000000 : ℝ), (4240880173/10000000000 : ℝ), (4494388603/10000000000 : ℝ)] ![(33316906946403/100000000000000 : ℝ), (1602930163401/5000000000000 : ℝ), (8656122442139/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365799919/10000000000 : ℝ)|^8327 ≤ (33316906946403/100000000000000 : ℝ)^6279
        have hw : |(4365799919/10000000000 : ℝ)|=(4365799919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4240880173/10000000000 : ℝ)|^8327 ≤ (1602930163401/5000000000000 : ℝ)^6279
        have hw : |(4240880173/10000000000 : ℝ)|=(4240880173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4494388603/10000000000 : ℝ)|^8327 ≤ (8656122442139/25000000000000 : ℝ)^6279
        have hw : |(4494388603/10000000000 : ℝ)|=(4494388603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s7_4 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2170721227/10000000000 : ℝ)*x 0 + (5265902231/10000000000 : ℝ)*x 1 + (2696442387/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170721227/10000000000 : ℝ)^8327 ≤ (13189443180603/100000000000000 : ℝ)^6279 := by
    have hnat : (2170721227 : ℕ)^8327*100000000000000^6279 ≤ 13189443180603^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170721227 10000000000 13189443180603 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265902231/10000000000 : ℝ)^8327 ≤ (2135976778511/5000000000000 : ℝ)^6279 := by
    have hnat : (5265902231 : ℕ)^8327*5000000000000^6279 ≤ 2135976778511^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265902231 10000000000 2135976778511 5000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696442387/5000000000 : ℝ)^8327 ≤ (44091021229439/100000000000000 : ℝ)^6279 := by
    have hnat : (2696442387 : ℕ)^8327*100000000000000^6279 ≤ 44091021229439^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696442387 5000000000 44091021229439 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2170721227/10000000000 : ℝ), (5265902231/10000000000 : ℝ), (2696442387/5000000000 : ℝ)] ![(13189443180603/100000000000000 : ℝ), (2135976778511/5000000000000 : ℝ), (44091021229439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2170721227/10000000000 : ℝ)|^8327 ≤ (13189443180603/100000000000000 : ℝ)^6279
        have hw : |(-2170721227/10000000000 : ℝ)|=(2170721227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265902231/10000000000 : ℝ)|^8327 ≤ (2135976778511/5000000000000 : ℝ)^6279
        have hw : |(5265902231/10000000000 : ℝ)|=(5265902231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696442387/5000000000 : ℝ)|^8327 ≤ (44091021229439/100000000000000 : ℝ)^6279
        have hw : |(2696442387/5000000000 : ℝ)|=(2696442387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s7_5 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328119619/2500000000 : ℝ)*x 0 + (-2108149189/10000000000 : ℝ)*x 1 + (5392884763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328119619/2500000000 : ℝ)^8327 ≤ (540266844653/1250000000000 : ℝ)^6279 := by
    have hnat : (1328119619 : ℕ)^8327*1250000000000^6279 ≤ 540266844653^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328119619 2500000000 540266844653 1250000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2108149189/10000000000 : ℝ)^8327 ≤ (634381565211/5000000000000 : ℝ)^6279 := by
    have hnat : (2108149189 : ℕ)^8327*5000000000000^6279 ≤ 634381565211^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108149189 10000000000 634381565211 5000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392884763/10000000000 : ℝ)^8327 ≤ (11022755277543/25000000000000 : ℝ)^6279 := by
    have hnat : (5392884763 : ℕ)^8327*25000000000000^6279 ≤ 11022755277543^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392884763 10000000000 11022755277543 25000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328119619/2500000000 : ℝ), (-2108149189/10000000000 : ℝ), (5392884763/10000000000 : ℝ)] ![(540266844653/1250000000000 : ℝ), (634381565211/5000000000000 : ℝ), (11022755277543/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328119619/2500000000 : ℝ)|^8327 ≤ (540266844653/1250000000000 : ℝ)^6279
        have hw : |(1328119619/2500000000 : ℝ)|=(1328119619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2108149189/10000000000 : ℝ)|^8327 ≤ (634381565211/5000000000000 : ℝ)^6279
        have hw : |(-2108149189/10000000000 : ℝ)|=(2108149189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392884763/10000000000 : ℝ)|^8327 ≤ (11022755277543/25000000000000 : ℝ)^6279
        have hw : |(5392884763/10000000000 : ℝ)|=(5392884763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s7_6 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312478471/10000000000 : ℝ)*x 0 + (1348221193/2500000000 : ℝ)*x 1 + (-2108149183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312478471/10000000000 : ℝ)^8327 ≤ (10805336879573/25000000000000 : ℝ)^6279 := by
    have hnat : (5312478471 : ℕ)^8327*25000000000000^6279 ≤ 10805336879573^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312478471 10000000000 10805336879573 25000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348221193/2500000000 : ℝ)^8327 ≤ (22045510603877/50000000000000 : ℝ)^6279 := by
    have hnat : (1348221193 : ℕ)^8327*50000000000000^6279 ≤ 22045510603877^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348221193 2500000000 22045510603877 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2108149183/10000000000 : ℝ)^8327 ≤ (12687631256331/100000000000000 : ℝ)^6279 := by
    have hnat : (2108149183 : ℕ)^8327*100000000000000^6279 ≤ 12687631256331^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108149183 10000000000 12687631256331 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312478471/10000000000 : ℝ), (1348221193/2500000000 : ℝ), (-2108149183/10000000000 : ℝ)] ![(10805336879573/25000000000000 : ℝ), (22045510603877/50000000000000 : ℝ), (12687631256331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312478471/10000000000 : ℝ)|^8327 ≤ (10805336879573/25000000000000 : ℝ)^6279
        have hw : |(5312478471/10000000000 : ℝ)|=(5312478471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348221193/2500000000 : ℝ)|^8327 ≤ (22045510603877/50000000000000 : ℝ)^6279
        have hw : |(1348221193/2500000000 : ℝ)|=(1348221193/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2108149183/10000000000 : ℝ)|^8327 ≤ (12687631256331/100000000000000 : ℝ)^6279
        have hw : |(-2108149183/10000000000 : ℝ)|=(2108149183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s7_7 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (436580967/1000000000 : ℝ)*x 0 + (4493751589/10000000000 : ℝ)*x 1 + (4241519491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436580967/1000000000 : ℝ)^8327 ≤ (33317005630743/100000000000000 : ℝ)^6279 := by
    have hnat : (436580967 : ℕ)^8327*100000000000000^6279 ≤ 33317005630743^6279*1000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436580967 1000000000 33317005630743 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4493751589/10000000000 : ℝ)^8327 ≤ (34617981735031/100000000000000 : ℝ)^6279 := by
    have hnat : (4493751589 : ℕ)^8327*100000000000000^6279 ≤ 34617981735031^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493751589 10000000000 34617981735031 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4241519491/10000000000 : ℝ)^8327 ≤ (2004063288901/6250000000000 : ℝ)^6279 := by
    have hnat : (4241519491 : ℕ)^8327*6250000000000^6279 ≤ 2004063288901^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241519491 10000000000 2004063288901 6250000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436580967/1000000000 : ℝ), (4493751589/10000000000 : ℝ), (4241519491/10000000000 : ℝ)] ![(33317005630743/100000000000000 : ℝ), (34617981735031/100000000000000 : ℝ), (2004063288901/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436580967/1000000000 : ℝ)|^8327 ≤ (33317005630743/100000000000000 : ℝ)^6279
        have hw : |(436580967/1000000000 : ℝ)|=(436580967/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4493751589/10000000000 : ℝ)|^8327 ≤ (34617981735031/100000000000000 : ℝ)^6279
        have hw : |(4493751589/10000000000 : ℝ)|=(4493751589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4241519491/10000000000 : ℝ)|^8327 ≤ (2004063288901/6250000000000 : ℝ)^6279
        have hw : |(4241519491/10000000000 : ℝ)|=(4241519491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1134_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2267/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5671/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2809/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3513/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2267/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3513/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2267/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3513/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2267/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3513/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2267/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3513/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2267/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3513/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2267/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2267/20000 : ℝ) ^ (4163/1024 : ℝ) ≤ (14315851794530739/100000000000000000000 : ℝ) := by
    have hpowers : (2267/20000 : ℝ)^4163 ≤ (14315851794530739/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2267 : ℕ)^4163*100000000000000000000^1024 ≤ 14315851794530739^1024*20000^4163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2267 20000 14315851794530739 100000000000000000000 4163 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2267/20000 : ℝ)) (X := (14315851794530739/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3513/25000 : ℝ) ^ (4163/1024 : ℝ) ≤ (34291725403458503/100000000000000000000 : ℝ) := by
    have hpowers : (3513/25000 : ℝ)^4163 ≤ (34291725403458503/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3513 : ℕ)^4163*100000000000000000000^1024 ≤ 34291725403458503^1024*25000^4163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3513 25000 34291725403458503 100000000000000000000 4163 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3513/25000 : ℝ)) (X := (34291725403458503/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014315851794530739/50000000000000000000 : ℝ) ≤ (2000140839299463/2000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (50014315851794530739/50000000000000000000 : ℝ)^1024 ≤ (2000140839299463/2000000000000000 : ℝ)^4163 := by
      have hnat : (50014315851794530739 : ℕ)^1024*2000000000000000^4163 ≤ 2000140839299463^4163*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014315851794530739 50000000000000000000 2000140839299463 2000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000140839299463/2000000000000000 : ℝ)) (X := (50014315851794530739/50000000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024303788598994621/50000000000000000000 : ℝ) ≤ (10001195412928527/10000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (50024303788598994621/50000000000000000000 : ℝ)^1024 ≤ (10001195412928527/10000000000000000 : ℝ)^4163 := by
      have hnat : (50024303788598994621 : ℕ)^1024*10000000000000000^4163 ≤ 10001195412928527^4163*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024303788598994621 50000000000000000000 10001195412928527 10000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001195412928527/10000000000000000 : ℝ)) (X := (50024303788598994621/50000000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034291725403458503/50000000000000000000 : ℝ) ≤ (10001686629359739/10000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (50034291725403458503/50000000000000000000 : ℝ)^1024 ≤ (10001686629359739/10000000000000000 : ℝ)^4163 := by
      have hnat : (50034291725403458503 : ℕ)^1024*10000000000000000^4163 ≤ 10001686629359739^4163*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034291725403458503 50000000000000000000 10001686629359739 10000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001686629359739/10000000000000000 : ℝ)) (X := (50034291725403458503/50000000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14315851794530739/100000000000000000000 : ℝ) ≤ ((417858114236732751/418000000000000000 : ℝ)+2*(9446469831/5225000000000 : ℝ)*(2267/20000 : ℝ))^(4163/1024 : ℝ) := by
    rw [show (417858114236732751/418000000000000000 : ℝ)+2*(9446469831/5225000000000 : ℝ)*(2267/20000 : ℝ)=(2000140839299463/2000000000000000 : ℝ) by norm_num, show 1+2*(14315851794530739/100000000000000000000 : ℝ)=(50014315851794530739/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34291725403458503/100000000000000000000 : ℝ)+(14315851794530739/100000000000000000000 : ℝ) ≤ ((417858114236732751/418000000000000000 : ℝ)+(9446469831/5225000000000 : ℝ)*((3513/25000 : ℝ)+(2267/20000 : ℝ)))^(4163/1024 : ℝ) := by
    rw [show (417858114236732751/418000000000000000 : ℝ)+(9446469831/5225000000000 : ℝ)*((3513/25000 : ℝ)+(2267/20000 : ℝ))=(10001195412928527/10000000000000000 : ℝ) by norm_num, show 1+(34291725403458503/100000000000000000000 : ℝ)+(14315851794530739/100000000000000000000 : ℝ)=(50024303788598994621/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34291725403458503/100000000000000000000 : ℝ) ≤ ((417858114236732751/418000000000000000 : ℝ)+2*(9446469831/5225000000000 : ℝ)*(3513/25000 : ℝ))^(4163/1024 : ℝ) := by
    rw [show (417858114236732751/418000000000000000 : ℝ)+2*(9446469831/5225000000000 : ℝ)*(3513/25000 : ℝ)=(10001686629359739/10000000000000000 : ℝ) by norm_num, show 1+2*(34291725403458503/100000000000000000000 : ℝ)=(50034291725403458503/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (417858114236732751/418000000000000000 : ℝ)*(X 1 0+X 2 0)+(9446469831/5225000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (2267/20000 : ℝ)) (hi := (3513/25000 : ℝ)) (c := (417858114236732751/418000000000000000 : ℝ)) (alpha := (9446469831/5225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (417858114236732751/418000000000000000 : ℝ)*(X 0 1+X 2 1)+(9446469831/5225000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (2267/20000 : ℝ)) (hi := (3513/25000 : ℝ)) (c := (417858114236732751/418000000000000000 : ℝ)) (alpha := (9446469831/5225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (417858114236732751/418000000000000000 : ℝ)*(X 0 2+X 1 2)+(9446469831/5225000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (2267/20000 : ℝ)) (hi := (3513/25000 : ℝ)) (c := (417858114236732751/418000000000000000 : ℝ)) (alpha := (9446469831/5225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1085358169/5000000000 : ℝ)*X 0 0+(5393206629/10000000000 : ℝ)*X 0 1+(5265581521/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334049603/625000000 : ℝ)*X 1 0+(-2235452417/10000000000 : ℝ)*X 1 1+(5265581531/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336198413/2500000000 : ℝ)*X 2 0+(2632790767/5000000000 : ℝ)*X 2 1+(-2235452409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4365799919/10000000000 : ℝ)*X 0 0+(4240880173/10000000000 : ℝ)*X 0 1+(4494388603/10000000000 : ℝ)*X 0 2+(4365799919/10000000000 : ℝ)*X 1 0+(4240880173/10000000000 : ℝ)*X 1 1+(4494388603/10000000000 : ℝ)*X 1 2+(4365799919/10000000000 : ℝ)*X 2 0+(4240880173/10000000000 : ℝ)*X 2 1+(4494388603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2170721227/10000000000 : ℝ)*X 0 0+(5265902231/10000000000 : ℝ)*X 0 1+(2696442387/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328119619/2500000000 : ℝ)*X 1 0+(-2108149189/10000000000 : ℝ)*X 1 1+(5392884763/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312478471/10000000000 : ℝ)*X 2 0+(1348221193/2500000000 : ℝ)*X 2 1+(-2108149183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((436580967/1000000000 : ℝ)*X 0 0+(4493751589/10000000000 : ℝ)*X 0 1+(4241519491/10000000000 : ℝ)*X 0 2+(436580967/1000000000 : ℝ)*X 1 0+(4493751589/10000000000 : ℝ)*X 1 1+(4241519491/10000000000 : ℝ)*X 1 2+(436580967/1000000000 : ℝ)*X 2 0+(4493751589/10000000000 : ℝ)*X 2 1+(4241519491/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (59974609244187236588039229/10450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1147935441/100000000000000 : ℝ)*(base19) + (6799833/625000000000 : ℝ)*(base23) + (35182743/100000000000000 : ℝ)*(lower2) + (137567033/100000000000000 : ℝ)*(upper3) + (12951187/12500000000000 : ℝ)*(upper5) + (5890094241098993/100000000000000 : ℝ)*(major0) + (5890094241098993/100000000000000 : ℝ)*(major1) + (5890094241098993/100000000000000 : ℝ)*(major2) + (1567096352645749/20000000000000 : ℝ)*(sp0) + (7835513116360377/100000000000000 : ℝ)*(sp1) + (7835513176322539/100000000000000 : ℝ)*(sp2) + (3944657441883723/100000000000000 : ℝ)*(sp3) + (16250533537/50000000000000 : ℝ)*(sp4) + (16584711871/100000000000000 : ℝ)*(sp7) + (1972337013297797/50000000000000 : ℝ)*(f.failure) + (7835514264295819/100000000000000 : ℝ)*(f.sum) + (1928841228777/1045000000000000000000000000 : ℝ)*base65 + (1039621546525073/200000000000000000000000000000 : ℝ)*base68 + (834643397325073/200000000000000000000000000000 : ℝ)*base70 + (117205152274927/200000000000000000000000000000 : ℝ)*base71 + (1704373483273/1045000000000000000000000000 : ℝ)*base74 + (29852350525073/200000000000000000000000000000 : ℝ)*base76 + (939442274125073/200000000000000000000000000000 : ℝ)*base78 + (349981971925073/200000000000000000000000000000 : ℝ)*base80 + (6251779066323/1045000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (20917337/2500000000000000000000 : ℝ)*base89 + (20917337/2500000000000000000000 : ℝ)*base91 + (20917337/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18701431074457802783249367/5225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (607344627/100000000000000 : ℝ)*(base19) + (33807261/5000000000000 : ℝ)*(base23) + (7702691/12500000000000 : ℝ)*(upper3) + (7053853/20000000000000 : ℝ)*(lower4) + (9578971/12500000000000 : ℝ)*(upper5) + (1479962490772539/25000000000000 : ℝ)*(major0) + (1479962490772539/25000000000000 : ℝ)*(major1) + (1479962490772539/25000000000000 : ℝ)*(major2) + (8229427043/50000000000000 : ℝ)*(sp1) + (18073710379/100000000000000 : ℝ)*(sp2) + (984387247456923/12500000000000 : ℝ)*(sp4) + (7875080913456671/100000000000000 : ℝ)*(sp5) + (1575015845959957/20000000000000 : ℝ)*(sp6) + (991150456804387/25000000000000 : ℝ)*(sp7) + (991150456804387/25000000000000 : ℝ)*(f.failure) + (984387247456923/12500000000000 : ℝ)*(f.sum) + (131395940131/65312500000000000000000000 : ℝ)*base66 + (472794008235621/50000000000000000000000000000 : ℝ)*base67 + (23156282164379/50000000000000000000000000000 : ℝ)*base70 + (569543867835621/50000000000000000000000000000 : ℝ)*base71 + (28508679449/1045000000000000000000000000 : ℝ)*base73 + (384224603314379/50000000000000000000000000000 : ℝ)*base76 + (208500318114379/50000000000000000000000000000 : ℝ)*base78 + (149463676864379/50000000000000000000000000000 : ℝ)*base80 + (111083354727/522500000000000000000000000 : ℝ)*base81 + (11047727/1250000000000000000000 : ℝ)*base89 + (11047727/1250000000000000000000 : ℝ)*base91 + (11047727/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1134_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3513/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2267/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5671/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2809/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1134_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1134_s8_0 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-434144289/2000000000 : ℝ)*x 0 + (67414201/125000000 : ℝ)*x 1 + (2632824399/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434144289/2000000000 : ℝ)^8327 ≤ (659472246861/5000000000000 : ℝ)^6279 := by
    have hnat : (434144289 : ℕ)^8327*5000000000000^6279 ≤ 659472246861^6279*2000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434144289 2000000000 659472246861 5000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67414201/125000000 : ℝ)^8327 ≤ (22046873010409/50000000000000 : ℝ)^6279 := by
    have hnat : (67414201 : ℕ)^8327*50000000000000^6279 ≤ 22046873010409^6279*125000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67414201 125000000 22046873010409 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632824399/5000000000 : ℝ)^8327 ≤ (21358404516067/50000000000000 : ℝ)^6279 := by
    have hnat : (2632824399 : ℕ)^8327*50000000000000^6279 ≤ 21358404516067^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632824399 5000000000 21358404516067 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-434144289/2000000000 : ℝ), (67414201/125000000 : ℝ), (2632824399/5000000000 : ℝ)] ![(659472246861/5000000000000 : ℝ), (22046873010409/50000000000000 : ℝ), (21358404516067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-434144289/2000000000 : ℝ)|^8327 ≤ (659472246861/5000000000000 : ℝ)^6279
        have hw : |(-434144289/2000000000 : ℝ)|=(434144289/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67414201/125000000 : ℝ)|^8327 ≤ (22046873010409/50000000000000 : ℝ)^6279
        have hw : |(67414201/125000000 : ℝ)|=(67414201/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632824399/5000000000 : ℝ)|^8327 ≤ (21358404516067/50000000000000 : ℝ)^6279
        have hw : |(2632824399/5000000000 : ℝ)|=(2632824399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s8_1 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344776199/10000000000 : ℝ)*x 0 + (-2235386583/10000000000 : ℝ)*x 1 + (5265648849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344776199/10000000000 : ℝ)^8327 ≤ (21785083595171/50000000000000 : ℝ)^6279 := by
    have hnat : (5344776199 : ℕ)^8327*50000000000000^6279 ≤ 21785083595171^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344776199 10000000000 21785083595171 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2235386583/10000000000 : ℝ)^8327 ≤ (107132993841/781250000000 : ℝ)^6279 := by
    have hnat : (2235386583 : ℕ)^8327*781250000000^6279 ≤ 107132993841^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2235386583 10000000000 107132993841 781250000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265648849/10000000000 : ℝ)^8327 ≤ (42716809580809/100000000000000 : ℝ)^6279 := by
    have hnat : (5265648849 : ℕ)^8327*100000000000000^6279 ≤ 42716809580809^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265648849 10000000000 42716809580809 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344776199/10000000000 : ℝ), (-2235386583/10000000000 : ℝ), (5265648849/10000000000 : ℝ)] ![(21785083595171/50000000000000 : ℝ), (107132993841/781250000000 : ℝ), (42716809580809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344776199/10000000000 : ℝ)|^8327 ≤ (21785083595171/50000000000000 : ℝ)^6279
        have hw : |(5344776199/10000000000 : ℝ)|=(5344776199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2235386583/10000000000 : ℝ)|^8327 ≤ (107132993841/781250000000 : ℝ)^6279
        have hw : |(-2235386583/10000000000 : ℝ)|=(2235386583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265648849/10000000000 : ℝ)|^8327 ≤ (42716809580809/100000000000000 : ℝ)^6279
        have hw : |(5265648849/10000000000 : ℝ)|=(5265648849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s8_2 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534477619/1000000000 : ℝ)*x 0 + (5265648837/10000000000 : ℝ)*x 1 + (-2235386611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534477619/1000000000 : ℝ)^8327 ≤ (10892541773261/25000000000000 : ℝ)^6279 := by
    have hnat : (534477619 : ℕ)^8327*25000000000000^6279 ≤ 10892541773261^6279*1000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534477619 1000000000 10892541773261 25000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265648837/10000000000 : ℝ)^8327 ≤ (42716809451709/100000000000000 : ℝ)^6279 := by
    have hnat : (5265648837 : ℕ)^8327*100000000000000^6279 ≤ 42716809451709^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265648837 10000000000 42716809451709 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2235386611/10000000000 : ℝ)^8327 ≤ (13713023439439/100000000000000 : ℝ)^6279 := by
    have hnat : (2235386611 : ℕ)^8327*100000000000000^6279 ≤ 13713023439439^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2235386611 10000000000 13713023439439 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534477619/1000000000 : ℝ), (5265648837/10000000000 : ℝ), (-2235386611/10000000000 : ℝ)] ![(10892541773261/25000000000000 : ℝ), (42716809451709/100000000000000 : ℝ), (13713023439439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534477619/1000000000 : ℝ)|^8327 ≤ (10892541773261/25000000000000 : ℝ)^6279
        have hw : |(534477619/1000000000 : ℝ)|=(534477619/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265648837/10000000000 : ℝ)|^8327 ≤ (42716809451709/100000000000000 : ℝ)^6279
        have hw : |(5265648837/10000000000 : ℝ)|=(5265648837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2235386611/10000000000 : ℝ)|^8327 ≤ (13713023439439/100000000000000 : ℝ)^6279
        have hw : |(-2235386611/10000000000 : ℝ)|=(2235386611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s8_3 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (545725427/1250000000 : ℝ)*x 0 + (33928133/80000000 : ℝ)*x 1 + (2247125623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545725427/1250000000 : ℝ)^8327 ≤ (8329235584387/25000000000000 : ℝ)^6279 := by
    have hnat : (545725427 : ℕ)^8327*25000000000000^6279 ≤ 8329235584387^6279*1250000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545725427 1250000000 8329235584387 25000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33928133/80000000 : ℝ)^8327 ≤ (32059971213729/100000000000000 : ℝ)^6279 := by
    have hnat : (33928133 : ℕ)^8327*100000000000000^6279 ≤ 32059971213729^6279*80000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33928133 80000000 32059971213729 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247125623/5000000000 : ℝ)^8327 ≤ (6924617287927/20000000000000 : ℝ)^6279 := by
    have hnat : (2247125623 : ℕ)^8327*20000000000000^6279 ≤ 6924617287927^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247125623 5000000000 6924617287927 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545725427/1250000000 : ℝ), (33928133/80000000 : ℝ), (2247125623/5000000000 : ℝ)] ![(8329235584387/25000000000000 : ℝ), (32059971213729/100000000000000 : ℝ), (6924617287927/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545725427/1250000000 : ℝ)|^8327 ≤ (8329235584387/25000000000000 : ℝ)^6279
        have hw : |(545725427/1250000000 : ℝ)|=(545725427/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33928133/80000000 : ℝ)|^8327 ≤ (32059971213729/100000000000000 : ℝ)^6279
        have hw : |(33928133/80000000 : ℝ)|=(33928133/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2247125623/5000000000 : ℝ)|^8327 ≤ (6924617287927/20000000000000 : ℝ)^6279
        have hw : |(2247125623/5000000000 : ℝ)|=(2247125623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s8_4 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2170726301/10000000000 : ℝ)*x 0 + (526596891/1000000000 : ℝ)*x 1 + (5392814841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170726301/10000000000 : ℝ)^8327 ≤ (13189484066273/100000000000000 : ℝ)^6279 := by
    have hnat : (2170726301 : ℕ)^8327*100000000000000^6279 ≤ 13189484066273^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170726301 10000000000 13189484066273 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526596891/1000000000 : ℝ)^8327 ≤ (42720252937869/100000000000000 : ℝ)^6279 := by
    have hnat : (526596891 : ℕ)^8327*100000000000000^6279 ≤ 42720252937869^6279*1000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526596891 1000000000 42720252937869 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392814841/10000000000 : ℝ)^8327 ≤ (22045131493281/50000000000000 : ℝ)^6279 := by
    have hnat : (5392814841 : ℕ)^8327*50000000000000^6279 ≤ 22045131493281^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392814841 10000000000 22045131493281 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2170726301/10000000000 : ℝ), (526596891/1000000000 : ℝ), (5392814841/10000000000 : ℝ)] ![(13189484066273/100000000000000 : ℝ), (42720252937869/100000000000000 : ℝ), (22045131493281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2170726301/10000000000 : ℝ)|^8327 ≤ (13189484066273/100000000000000 : ℝ)^6279
        have hw : |(-2170726301/10000000000 : ℝ)|=(2170726301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526596891/1000000000 : ℝ)|^8327 ≤ (42720252937869/100000000000000 : ℝ)^6279
        have hw : |(526596891/1000000000 : ℝ)|=(526596891/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392814841/10000000000 : ℝ)|^8327 ≤ (22045131493281/50000000000000 : ℝ)^6279
        have hw : |(5392814841/10000000000 : ℝ)|=(5392814841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s8_5 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312495781/10000000000 : ℝ)*x 0 + (-2108220527/10000000000 : ℝ)*x 1 + (1348203757/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312495781/10000000000 : ℝ)^8327 ≤ (21610767141863/50000000000000 : ℝ)^6279 := by
    have hnat : (5312495781 : ℕ)^8327*50000000000000^6279 ≤ 21610767141863^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312495781 10000000000 21610767141863 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2108220527/10000000000 : ℝ)^8327 ≤ (3172050170533/25000000000000 : ℝ)^6279 := by
    have hnat : (2108220527 : ℕ)^8327*25000000000000^6279 ≤ 3172050170533^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108220527 10000000000 3172050170533 25000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348203757/2500000000 : ℝ)^8327 ≤ (44090265014091/100000000000000 : ℝ)^6279 := by
    have hnat : (1348203757 : ℕ)^8327*100000000000000^6279 ≤ 44090265014091^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348203757 2500000000 44090265014091 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312495781/10000000000 : ℝ), (-2108220527/10000000000 : ℝ), (1348203757/2500000000 : ℝ)] ![(21610767141863/50000000000000 : ℝ), (3172050170533/25000000000000 : ℝ), (44090265014091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312495781/10000000000 : ℝ)|^8327 ≤ (21610767141863/50000000000000 : ℝ)^6279
        have hw : |(5312495781/10000000000 : ℝ)|=(5312495781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2108220527/10000000000 : ℝ)|^8327 ≤ (3172050170533/25000000000000 : ℝ)^6279
        have hw : |(-2108220527/10000000000 : ℝ)|=(2108220527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348203757/2500000000 : ℝ)|^8327 ≤ (44090265014091/100000000000000 : ℝ)^6279
        have hw : |(1348203757/2500000000 : ℝ)|=(1348203757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s8_6 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (166015499/312500000 : ℝ)*x 0 + (5392814837/10000000000 : ℝ)*x 1 + (-1054110267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166015499/312500000 : ℝ)^8327 ≤ (8644307260271/20000000000000 : ℝ)^6279 := by
    have hnat : (166015499 : ℕ)^8327*20000000000000^6279 ≤ 8644307260271^6279*312500000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166015499 312500000 8644307260271 20000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392814837/10000000000 : ℝ)^8327 ≤ (44090262943193/100000000000000 : ℝ)^6279 := by
    have hnat : (5392814837 : ℕ)^8327*100000000000000^6279 ≤ 44090262943193^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392814837 10000000000 44090262943193 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054110267/5000000000 : ℝ)^8327 ≤ (6344100369001/50000000000000 : ℝ)^6279 := by
    have hnat : (1054110267 : ℕ)^8327*50000000000000^6279 ≤ 6344100369001^6279*5000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054110267 5000000000 6344100369001 50000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166015499/312500000 : ℝ), (5392814837/10000000000 : ℝ), (-1054110267/5000000000 : ℝ)] ![(8644307260271/20000000000000 : ℝ), (44090262943193/100000000000000 : ℝ), (6344100369001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166015499/312500000 : ℝ)|^8327 ≤ (8644307260271/20000000000000 : ℝ)^6279
        have hw : |(166015499/312500000 : ℝ)|=(166015499/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392814837/10000000000 : ℝ)|^8327 ≤ (44090262943193/100000000000000 : ℝ)^6279
        have hw : |(5392814837/10000000000 : ℝ)|=(5392814837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1054110267/5000000000 : ℝ)|^8327 ≤ (6344100369001/50000000000000 : ℝ)^6279
        have hw : |(-1054110267/5000000000 : ℝ)|=(1054110267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1134_s8_7 (p : ℝ) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (109145327/250000000 : ℝ)*x 0 + (1123403909/2500000000 : ℝ)*x 1 + (4241654587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (109145327/250000000 : ℝ)^8327 ≤ (8329260035359/25000000000000 : ℝ)^6279 := by
    have hnat : (109145327 : ℕ)^8327*25000000000000^6279 ≤ 8329260035359^6279*250000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109145327 250000000 8329260035359 25000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123403909/2500000000 : ℝ)^8327 ≤ (34616592814437/100000000000000 : ℝ)^6279 := by
    have hnat : (1123403909 : ℕ)^8327*100000000000000^6279 ≤ 34616592814437^6279*2500000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123403909 2500000000 34616592814437 100000000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4241654587/10000000000 : ℝ)^8327 ≤ (160331835203/500000000000 : ℝ)^6279 := by
    have hnat : (4241654587 : ℕ)^8327*500000000000^6279 ≤ 160331835203^6279*10000000000^8327 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4241654587 10000000000 160331835203 500000000000 8327 6279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8327/2048 : ℝ)) 8327 6279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(109145327/250000000 : ℝ), (1123403909/2500000000 : ℝ), (4241654587/10000000000 : ℝ)] ![(8329260035359/25000000000000 : ℝ), (34616592814437/100000000000000 : ℝ), (160331835203/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(109145327/250000000 : ℝ)|^8327 ≤ (8329260035359/25000000000000 : ℝ)^6279
        have hw : |(109145327/250000000 : ℝ)|=(109145327/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1123403909/2500000000 : ℝ)|^8327 ≤ (34616592814437/100000000000000 : ℝ)^6279
        have hw : |(1123403909/2500000000 : ℝ)|=(1123403909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4241654587/10000000000 : ℝ)|^8327 ≤ (160331835203/500000000000 : ℝ)^6279
        have hw : |(4241654587/10000000000 : ℝ)|=(4241654587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1134_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2809/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5671/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11343/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3511/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2809/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5671/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2809/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5671/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2809/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5671/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2809/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5671/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2809/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5671/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2809/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5671/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5671/50000 : ℝ) ^ (4163/1024 : ℝ) ≤ (3587956914362907/25000000000000000000 : ℝ) := by
    have hpowers : (5671/50000 : ℝ)^4163 ≤ (3587956914362907/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5671 : ℕ)^4163*25000000000000000000^1024 ≤ 3587956914362907^1024*50000^4163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5671 50000 3587956914362907 25000000000000000000 4163 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5671/50000 : ℝ)) (X := (3587956914362907/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2809/20000 : ℝ) ^ (4163/1024 : ℝ) ≤ (684446621157649/2000000000000000000 : ℝ) := by
    have hpowers : (2809/20000 : ℝ)^4163 ≤ (684446621157649/2000000000000000000 : ℝ)^1024 := by
      have hnat : (2809 : ℕ)^4163*2000000000000000000^1024 ≤ 684446621157649^1024*20000^4163 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2809 20000 684446621157649 2000000000000000000 4163 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2809/20000 : ℝ)) (X := (684446621157649/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503587956914362907/12500000000000000000 : ℝ) ≤ (10000705965957917/10000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (12503587956914362907/12500000000000000000 : ℝ)^1024 ≤ (10000705965957917/10000000000000000 : ℝ)^4163 := by
      have hnat : (12503587956914362907 : ℕ)^1024*10000000000000000^4163 ≤ 10000705965957917^4163*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503587956914362907 12500000000000000000 10000705965957917 10000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000705965957917/10000000000000000 : ℝ)) (X := (12503587956914362907/12500000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024287079357667039/50000000000000000000 : ℝ) ≤ (1000119459121357/1000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (50024287079357667039/50000000000000000000 : ℝ)^1024 ≤ (1000119459121357/1000000000000000 : ℝ)^4163 := by
      have hnat : (50024287079357667039 : ℕ)^1024*1000000000000000^4163 ≤ 1000119459121357^4163*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024287079357667039 50000000000000000000 1000119459121357 1000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000119459121357/1000000000000000 : ℝ)) (X := (50024287079357667039/50000000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000684446621157649/1000000000000000000 : ℝ) ≤ (10001683216469223/10000000000000000 : ℝ) ^ (4163/1024 : ℝ) := by
    have hpowers : (1000684446621157649/1000000000000000000 : ℝ)^1024 ≤ (10001683216469223/10000000000000000 : ℝ)^4163 := by
      have hnat : (1000684446621157649 : ℕ)^1024*10000000000000000^4163 ≤ 10001683216469223^4163*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000684446621157649 1000000000000000000 10001683216469223 10000000000000000 1024 4163 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001683216469223/10000000000000000 : ℝ)) (X := (1000684446621157649/1000000000000000000 : ℝ)) (by norm_num) 4163 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3587956914362907/25000000000000000000 : ℝ) ≤ ((509826872654434283/510000000000000000 : ℝ)+2*(488625255653/270300000000000 : ℝ)*(5671/50000 : ℝ))^(4163/1024 : ℝ) := by
    rw [show (509826872654434283/510000000000000000 : ℝ)+2*(488625255653/270300000000000 : ℝ)*(5671/50000 : ℝ)=(10000705965957917/10000000000000000 : ℝ) by norm_num, show 1+2*(3587956914362907/25000000000000000000 : ℝ)=(12503587956914362907/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(684446621157649/2000000000000000000 : ℝ)+(3587956914362907/25000000000000000000 : ℝ) ≤ ((509826872654434283/510000000000000000 : ℝ)+(488625255653/270300000000000 : ℝ)*((2809/20000 : ℝ)+(5671/50000 : ℝ)))^(4163/1024 : ℝ) := by
    rw [show (509826872654434283/510000000000000000 : ℝ)+(488625255653/270300000000000 : ℝ)*((2809/20000 : ℝ)+(5671/50000 : ℝ))=(1000119459121357/1000000000000000 : ℝ) by norm_num, show 1+(684446621157649/2000000000000000000 : ℝ)+(3587956914362907/25000000000000000000 : ℝ)=(50024287079357667039/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(684446621157649/2000000000000000000 : ℝ) ≤ ((509826872654434283/510000000000000000 : ℝ)+2*(488625255653/270300000000000 : ℝ)*(2809/20000 : ℝ))^(4163/1024 : ℝ) := by
    rw [show (509826872654434283/510000000000000000 : ℝ)+2*(488625255653/270300000000000 : ℝ)*(2809/20000 : ℝ)=(10001683216469223/10000000000000000 : ℝ) by norm_num, show 1+2*(684446621157649/2000000000000000000 : ℝ)=(1000684446621157649/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (509826872654434283/510000000000000000 : ℝ)*(X 1 0+X 2 0)+(488625255653/270300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (5671/50000 : ℝ)) (hi := (2809/20000 : ℝ)) (c := (509826872654434283/510000000000000000 : ℝ)) (alpha := (488625255653/270300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (509826872654434283/510000000000000000 : ℝ)*(X 0 1+X 2 1)+(488625255653/270300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (5671/50000 : ℝ)) (hi := (2809/20000 : ℝ)) (c := (509826872654434283/510000000000000000 : ℝ)) (alpha := (488625255653/270300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (509826872654434283/510000000000000000 : ℝ)*(X 0 2+X 1 2)+(488625255653/270300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4163/1024 : ℝ)) (lo := (5671/50000 : ℝ)) (hi := (2809/20000 : ℝ)) (c := (509826872654434283/510000000000000000 : ℝ)) (alpha := (488625255653/270300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-434144289/2000000000 : ℝ)*X 0 0+(67414201/125000000 : ℝ)*X 0 1+(2632824399/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344776199/10000000000 : ℝ)*X 1 0+(-2235386583/10000000000 : ℝ)*X 1 1+(5265648849/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534477619/1000000000 : ℝ)*X 2 0+(5265648837/10000000000 : ℝ)*X 2 1+(-2235386611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((545725427/1250000000 : ℝ)*X 0 0+(33928133/80000000 : ℝ)*X 0 1+(2247125623/5000000000 : ℝ)*X 0 2+(545725427/1250000000 : ℝ)*X 1 0+(33928133/80000000 : ℝ)*X 1 1+(2247125623/5000000000 : ℝ)*X 1 2+(545725427/1250000000 : ℝ)*X 2 0+(33928133/80000000 : ℝ)*X 2 1+(2247125623/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2170726301/10000000000 : ℝ)*X 0 0+(526596891/1000000000 : ℝ)*X 0 1+(5392814841/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312495781/10000000000 : ℝ)*X 1 0+(-2108220527/10000000000 : ℝ)*X 1 1+(1348203757/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((166015499/312500000 : ℝ)*X 2 0+(5392814837/10000000000 : ℝ)*X 2 1+(-1054110267/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((109145327/250000000 : ℝ)*X 0 0+(1123403909/2500000000 : ℝ)*X 0 1+(4241654587/10000000000 : ℝ)*X 0 2+(109145327/250000000 : ℝ)*X 1 0+(1123403909/2500000000 : ℝ)*X 1 1+(4241654587/10000000000 : ℝ)*X 1 2+(109145327/250000000 : ℝ)*X 2 0+(1123403909/2500000000 : ℝ)*X 2 1+(4241654587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1134_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (336073294642417674302023/34000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (191694849/10000000000000 : ℝ)*(base19) + (1790120439/100000000000000 : ℝ)*(base23) + (7590891/12500000000000 : ℝ)*(lower2) + (54003547/20000000000000 : ℝ)*(upper3) + (34672059/25000000000000 : ℝ)*(upper5) + (23585985568219/400000000000 : ℝ)*(major0) + (23585985568219/400000000000 : ℝ)*(major1) + (23585985568219/400000000000 : ℝ)*(major2) + (3921988771547133/50000000000000 : ℝ)*(sp0) + (122562951654687/1562500000000 : ℝ)*(sp1) + (392201451636401/5000000000000 : ℝ)*(sp2) + (789786541539807/20000000000000 : ℝ)*(sp3) + (53279754193/100000000000000 : ℝ)*(sp4) + (14462039187/50000000000000 : ℝ)*(sp7) + (394896163177741/10000000000000 : ℝ)*(f.failure) + (3922015411424229/50000000000000 : ℝ)*(f.sum) + (19314160258601/2703000000000000000000000000 : ℝ)*base66 + (1503990714605231/212000000000000000000000000000 : ℝ)*base67 + (1201456097645231/212000000000000000000000000000 : ℝ)*base69 + (716362492449231/212000000000000000000000000000 : ℝ)*base71 + (2233254103267/540600000000000000000000000 : ℝ)*base74 + (2472954452433231/212000000000000000000000000000 : ℝ)*base75 + (1912560927166769/212000000000000000000000000000 : ℝ)*base78 + (587273921354769/212000000000000000000000000000 : ℝ)*base80 + (5588599533983/1351500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (6503361/500000000000000000000 : ℝ)*base89 + (6503361/500000000000000000000 : ℝ)*base91 + (6503361/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2263828275725227272171/265000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1183157769/100000000000000 : ℝ)*(base19) + (64822677/4000000000000 : ℝ)*(base23) + (12389379/2500000000000 : ℝ)*(lower1) + (24618709/12500000000000 : ℝ)*(upper3) + (58213517/100000000000000 : ℝ)*(lower4) + (104316813/100000000000000 : ℝ)*(upper5) + (740774283879131/12500000000000 : ℝ)*(major0) + (740774283879131/12500000000000 : ℝ)*(major1) + (740774283879131/12500000000000 : ℝ)*(major2) + (4141513793/50000000000000 : ℝ)*(sp2) + (7883537563139291/100000000000000 : ℝ)*(sp4) + (7883536379981521/100000000000000 : ℝ)*(sp5) + (7883527659544779/100000000000000 : ℝ)*(sp6) + (992212673542127/25000000000000 : ℝ)*(sp7) + (992212673542127/25000000000000 : ℝ)*(f.failure) + (7883537563139291/100000000000000 : ℝ)*(f.sum) + (973546189523/795000000000000000000000000 : ℝ)*base66 + (36567032826198081/6625000000000000000000000000000 : ℝ)*base68 + (107043981768323081/6625000000000000000000000000000 : ℝ)*base70 + (454054539288926919/6625000000000000000000000000000 : ℝ)*base71 + (2773758079763/795000000000000000000000000 : ℝ)*base74 + (610071989179051919/6625000000000000000000000000000 : ℝ)*base75 + (25095955278551919/6625000000000000000000000000000 : ℝ)*base77 + (6830459930573081/6625000000000000000000000000000 : ℝ)*base80 + (798000631487/198750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4347733/1250000000000000000000 : ℝ)*base90 + (4347733/1250000000000000000000 : ℝ)*base92 + (4347733/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1134_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2809/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5671/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11343/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3511/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1134_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1134_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11303/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11343/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3511/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1134_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1134_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1134_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4163/1024 : ℝ) ≤ p) (hpb : p ≤ (8327/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74658821/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2817/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11303/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11343/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3511/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1134_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
