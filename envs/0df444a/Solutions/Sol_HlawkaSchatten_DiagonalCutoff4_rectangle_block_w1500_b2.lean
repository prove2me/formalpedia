-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1500_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:52:20.883382+00:00
-- url     : https://prove2.me/submissions/07271d6b-9179-497a-8d6b-7a067a8cf96b

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
theorem support_rectangle_w1500_s6_0 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1885891609/10000000000 : ℝ)*x 0 + (5434797817/10000000000 : ℝ)*x 1 + (5217008157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1885891609/10000000000 : ℝ)^4497 ≤ (11532030076243/100000000000000 : ℝ)^3473 := by
    have hnat : (1885891609 : ℕ)^4497*100000000000000^3473 ≤ 11532030076243^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1885891609 10000000000 11532030076243 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5434797817/10000000000 : ℝ)^4497 ≤ (5675619861487/12500000000000 : ℝ)^3473 := by
    have hnat : (5434797817 : ℕ)^4497*12500000000000^3473 ≤ 5675619861487^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5434797817 10000000000 5675619861487 12500000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5217008157/10000000000 : ℝ)^4497 ≤ (1076575275213/2500000000000 : ℝ)^3473 := by
    have hnat : (5217008157 : ℕ)^4497*2500000000000^3473 ≤ 1076575275213^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217008157 10000000000 1076575275213 2500000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1885891609/10000000000 : ℝ), (5434797817/10000000000 : ℝ), (5217008157/10000000000 : ℝ)] ![(11532030076243/100000000000000 : ℝ), (5675619861487/12500000000000 : ℝ), (1076575275213/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1885891609/10000000000 : ℝ)|^4497 ≤ (11532030076243/100000000000000 : ℝ)^3473
        have hw : |(-1885891609/10000000000 : ℝ)|=(1885891609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5434797817/10000000000 : ℝ)|^4497 ≤ (5675619861487/12500000000000 : ℝ)^3473
        have hw : |(5434797817/10000000000 : ℝ)|=(5434797817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5217008157/10000000000 : ℝ)|^4497 ≤ (1076575275213/2500000000000 : ℝ)^3473
        have hw : |(5217008157/10000000000 : ℝ)|=(5217008157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_s6_1 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338062369/2500000000 : ℝ)*x 0 + (-1997460117/10000000000 : ℝ)*x 1 + (1304252049/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338062369/2500000000 : ℝ)^4497 ≤ (22256988077511/50000000000000 : ℝ)^3473 := by
    have hnat : (1338062369 : ℕ)^4497*50000000000000^3473 ≤ 22256988077511^3473*2500000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338062369 2500000000 22256988077511 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1997460117/10000000000 : ℝ)^4497 ≤ (6211506206419/50000000000000 : ℝ)^3473 := by
    have hnat : (1997460117 : ℕ)^4497*50000000000000^3473 ≤ 6211506206419^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997460117 10000000000 6211506206419 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304252049/2500000000 : ℝ)^4497 ≤ (43063011425357/100000000000000 : ℝ)^3473 := by
    have hnat : (1304252049 : ℕ)^4497*100000000000000^3473 ≤ 43063011425357^3473*2500000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304252049 2500000000 43063011425357 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338062369/2500000000 : ℝ), (-1997460117/10000000000 : ℝ), (1304252049/2500000000 : ℝ)] ![(22256988077511/50000000000000 : ℝ), (6211506206419/50000000000000 : ℝ), (43063011425357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338062369/2500000000 : ℝ)|^4497 ≤ (22256988077511/50000000000000 : ℝ)^3473
        have hw : |(1338062369/2500000000 : ℝ)|=(1338062369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1997460117/10000000000 : ℝ)|^4497 ≤ (6211506206419/50000000000000 : ℝ)^3473
        have hw : |(-1997460117/10000000000 : ℝ)|=(1997460117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304252049/2500000000 : ℝ)|^4497 ≤ (43063011425357/100000000000000 : ℝ)^3473
        have hw : |(1304252049/2500000000 : ℝ)|=(1304252049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_s6_2 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669031157/1250000000 : ℝ)*x 0 + (1043401677/2000000000 : ℝ)*x 1 + (-1997460159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669031157/1250000000 : ℝ)^4497 ≤ (44513973785827/100000000000000 : ℝ)^3473 := by
    have hnat : (669031157 : ℕ)^4497*100000000000000^3473 ≤ 44513973785827^3473*1250000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669031157 1250000000 44513973785827 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043401677/2000000000 : ℝ)^4497 ≤ (4306301344541/10000000000000 : ℝ)^3473 := by
    have hnat : (1043401677 : ℕ)^4497*10000000000000^3473 ≤ 4306301344541^3473*2000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043401677 2000000000 4306301344541 10000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1997460159/10000000000 : ℝ)^4497 ≤ (12423012751071/100000000000000 : ℝ)^3473 := by
    have hnat : (1997460159 : ℕ)^4497*100000000000000^3473 ≤ 12423012751071^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997460159 10000000000 12423012751071 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669031157/1250000000 : ℝ), (1043401677/2000000000 : ℝ), (-1997460159/10000000000 : ℝ)] ![(44513973785827/100000000000000 : ℝ), (4306301344541/10000000000000 : ℝ), (12423012751071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669031157/1250000000 : ℝ)|^4497 ≤ (44513973785827/100000000000000 : ℝ)^3473
        have hw : |(669031157/1250000000 : ℝ)|=(669031157/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043401677/2000000000 : ℝ)|^4497 ≤ (4306301344541/10000000000000 : ℝ)^3473
        have hw : |(1043401677/2000000000 : ℝ)|=(1043401677/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1997460159/10000000000 : ℝ)|^4497 ≤ (12423012751071/100000000000000 : ℝ)^3473
        have hw : |(-1997460159/10000000000 : ℝ)|=(1997460159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_s6_3 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2137696679/5000000000 : ℝ)*x 0 + (2018282177/5000000000 : ℝ)*x 1 + (4526247157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2137696679/5000000000 : ℝ)^4497 ≤ (33279045980197/100000000000000 : ℝ)^3473 := by
    have hnat : (2137696679 : ℕ)^4497*100000000000000^3473 ≤ 33279045980197^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2137696679 5000000000 33279045980197 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2018282177/5000000000 : ℝ)^4497 ≤ (30892003661363/100000000000000 : ℝ)^3473 := by
    have hnat : (2018282177 : ℕ)^4497*100000000000000^3473 ≤ 30892003661363^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2018282177 5000000000 30892003661363 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4526247157/10000000000 : ℝ)^4497 ≤ (7165790069903/20000000000000 : ℝ)^3473 := by
    have hnat : (4526247157 : ℕ)^4497*20000000000000^3473 ≤ 7165790069903^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4526247157 10000000000 7165790069903 20000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2137696679/5000000000 : ℝ), (2018282177/5000000000 : ℝ), (4526247157/10000000000 : ℝ)] ![(33279045980197/100000000000000 : ℝ), (30892003661363/100000000000000 : ℝ), (7165790069903/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2137696679/5000000000 : ℝ)|^4497 ≤ (33279045980197/100000000000000 : ℝ)^3473
        have hw : |(2137696679/5000000000 : ℝ)|=(2137696679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2018282177/5000000000 : ℝ)|^4497 ≤ (30892003661363/100000000000000 : ℝ)^3473
        have hw : |(2018282177/5000000000 : ℝ)|=(2018282177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4526247157/10000000000 : ℝ)|^4497 ≤ (7165790069903/20000000000000 : ℝ)^3473
        have hw : |(4526247157/10000000000 : ℝ)|=(4526247157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_s6_4 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-235740113/1250000000 : ℝ)*x 0 + (5218126749/10000000000 : ℝ)*x 1 + (2716835561/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (235740113/1250000000 : ℝ)^4497 ≤ (5766131015061/50000000000000 : ℝ)^3473 := by
    have hnat : (235740113 : ℕ)^4497*50000000000000^3473 ≤ 5766131015061^3473*1250000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235740113 1250000000 5766131015061 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218126749/10000000000 : ℝ)^4497 ≤ (43074967022583/100000000000000 : ℝ)^3473 := by
    have hnat : (5218126749 : ℕ)^4497*100000000000000^3473 ≤ 43074967022583^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218126749 10000000000 43074967022583 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2716835561/5000000000 : ℝ)^4497 ≤ (22696385464943/50000000000000 : ℝ)^3473 := by
    have hnat : (2716835561 : ℕ)^4497*50000000000000^3473 ≤ 22696385464943^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716835561 5000000000 22696385464943 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-235740113/1250000000 : ℝ), (5218126749/10000000000 : ℝ), (2716835561/5000000000 : ℝ)] ![(5766131015061/50000000000000 : ℝ), (43074967022583/100000000000000 : ℝ), (22696385464943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-235740113/1250000000 : ℝ)|^4497 ≤ (5766131015061/50000000000000 : ℝ)^3473
        have hw : |(-235740113/1250000000 : ℝ)|=(235740113/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218126749/10000000000 : ℝ)|^4497 ≤ (43074967022583/100000000000000 : ℝ)^3473
        have hw : |(5218126749/10000000000 : ℝ)|=(5218126749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2716835561/5000000000 : ℝ)|^4497 ≤ (22696385464943/50000000000000 : ℝ)^3473
        have hw : |(2716835561/5000000000 : ℝ)|=(2716835561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_s6_5 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295183007/10000000000 : ℝ)*x 0 + (-1780797321/10000000000 : ℝ)*x 1 + (5433671101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295183007/10000000000 : ℝ)^4497 ≤ (21950195923803/50000000000000 : ℝ)^3473 := by
    have hnat : (5295183007 : ℕ)^4497*50000000000000^3473 ≤ 21950195923803^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295183007 10000000000 21950195923803 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1780797321/10000000000 : ℝ)^4497 ≤ (10706837435621/100000000000000 : ℝ)^3473 := by
    have hnat : (1780797321 : ℕ)^4497*100000000000000^3473 ≤ 10706837435621^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1780797321 10000000000 10706837435621 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433671101/10000000000 : ℝ)^4497 ≤ (45392770702727/100000000000000 : ℝ)^3473 := by
    have hnat : (5433671101 : ℕ)^4497*100000000000000^3473 ≤ 45392770702727^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433671101 10000000000 45392770702727 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295183007/10000000000 : ℝ), (-1780797321/10000000000 : ℝ), (5433671101/10000000000 : ℝ)] ![(21950195923803/50000000000000 : ℝ), (10706837435621/100000000000000 : ℝ), (45392770702727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295183007/10000000000 : ℝ)|^4497 ≤ (21950195923803/50000000000000 : ℝ)^3473
        have hw : |(5295183007/10000000000 : ℝ)|=(5295183007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1780797321/10000000000 : ℝ)|^4497 ≤ (10706837435621/100000000000000 : ℝ)^3473
        have hw : |(-1780797321/10000000000 : ℝ)|=(1780797321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433671101/10000000000 : ℝ)|^4497 ≤ (45392770702727/100000000000000 : ℝ)^3473
        have hw : |(5433671101/10000000000 : ℝ)|=(5433671101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_s6_6 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647591497/5000000000 : ℝ)*x 0 + (5433671139/10000000000 : ℝ)*x 1 + (-890398643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647591497/5000000000 : ℝ)^4497 ≤ (878007834161/2000000000000 : ℝ)^3473 := by
    have hnat : (2647591497 : ℕ)^4497*2000000000000^3473 ≤ 878007834161^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647591497 5000000000 878007834161 2000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433671139/10000000000 : ℝ)^4497 ≤ (45392771113777/100000000000000 : ℝ)^3473 := by
    have hnat : (5433671139 : ℕ)^4497*100000000000000^3473 ≤ 45392771113777^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433671139 10000000000 45392771113777 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (890398643/5000000000 : ℝ)^4497 ≤ (5353418581571/50000000000000 : ℝ)^3473 := by
    have hnat : (890398643 : ℕ)^4497*50000000000000^3473 ≤ 5353418581571^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890398643 5000000000 5353418581571 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647591497/5000000000 : ℝ), (5433671139/10000000000 : ℝ), (-890398643/5000000000 : ℝ)] ![(878007834161/2000000000000 : ℝ), (45392771113777/100000000000000 : ℝ), (5353418581571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647591497/5000000000 : ℝ)|^4497 ≤ (878007834161/2000000000000 : ℝ)^3473
        have hw : |(2647591497/5000000000 : ℝ)|=(2647591497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433671139/10000000000 : ℝ)|^4497 ≤ (45392771113777/100000000000000 : ℝ)^3473
        have hw : |(5433671139/10000000000 : ℝ)|=(5433671139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-890398643/5000000000 : ℝ)|^4497 ≤ (5353418581571/50000000000000 : ℝ)^3473
        have hw : |(-890398643/5000000000 : ℝ)|=(890398643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_s6_7 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2137729849/5000000000 : ℝ)*x 0 + (4523732631/10000000000 : ℝ)*x 1 + (252443581/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2137729849/5000000000 : ℝ)^4497 ≤ (33279714615579/100000000000000 : ℝ)^3473 := by
    have hnat : (2137729849 : ℕ)^4497*100000000000000^3473 ≤ 33279714615579^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2137729849 5000000000 33279714615579 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4523732631/10000000000 : ℝ)^4497 ≤ (35803179159077/100000000000000 : ℝ)^3473 := by
    have hnat : (4523732631 : ℕ)^4497*100000000000000^3473 ≤ 35803179159077^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523732631 10000000000 35803179159077 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (252443581/625000000 : ℝ)^4497 ≤ (15458553102027/50000000000000 : ℝ)^3473 := by
    have hnat : (252443581 : ℕ)^4497*50000000000000^3473 ≤ 15458553102027^3473*625000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252443581 625000000 15458553102027 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2137729849/5000000000 : ℝ), (4523732631/10000000000 : ℝ), (252443581/625000000 : ℝ)] ![(33279714615579/100000000000000 : ℝ), (35803179159077/100000000000000 : ℝ), (15458553102027/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2137729849/5000000000 : ℝ)|^4497 ≤ (33279714615579/100000000000000 : ℝ)^3473
        have hw : |(2137729849/5000000000 : ℝ)|=(2137729849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4523732631/10000000000 : ℝ)|^4497 ≤ (35803179159077/100000000000000 : ℝ)^3473
        have hw : |(4523732631/10000000000 : ℝ)|=(4523732631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(252443581/625000000 : ℝ)|^4497 ≤ (15458553102027/50000000000000 : ℝ)^3473
        have hw : |(252443581/625000000 : ℝ)|=(252443581/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1500_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32484241/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2717/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10869/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (387/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2717/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15481/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2717/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2717/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15481/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2717/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2717/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15481/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2717/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2717/25000 : ℝ) ^ (4495/1024 : ℝ) ≤ (146884421418701/2500000000000000000 : ℝ) := by
    have hpowers : (2717/25000 : ℝ)^4495 ≤ (146884421418701/2500000000000000000 : ℝ)^1024 := by
      have hnat : (2717 : ℕ)^4495*2500000000000000000^1024 ≤ 146884421418701^1024*25000^4495 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2717 25000 146884421418701 2500000000000000000 4495 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2717/25000 : ℝ)) (X := (146884421418701/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4495 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15481/100000 : ℝ) ^ (4495/1024 : ℝ) ≤ (27765307842660259/100000000000000000000 : ℝ) := by
    have hpowers : (15481/100000 : ℝ)^4495 ≤ (27765307842660259/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15481 : ℕ)^4495*100000000000000000000^1024 ≤ 27765307842660259^1024*100000^4495 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15481 100000 27765307842660259 100000000000000000000 4495 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15481/100000 : ℝ)) (X := (27765307842660259/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4495 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250146884421418701/1250000000000000000 : ℝ) ≤ (1250033460027597/1250000000000000 : ℝ) ^ (4495/1024 : ℝ) := by
    have hpowers : (1250146884421418701/1250000000000000000 : ℝ)^1024 ≤ (1250033460027597/1250000000000000 : ℝ)^4495 := by
      have hnat : (1250146884421418701 : ℕ)^1024*1250000000000000^4495 ≤ 1250033460027597^4495*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250146884421418701 1250000000000000000 1250033460027597 1250000000000000 1024 4495 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250033460027597/1250000000000000 : ℝ)) (X := (1250146884421418701/1250000000000000000 : ℝ)) (by norm_num) 4495 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100033640684699408299/100000000000000000000 : ℝ) ≤ (5000383132232781/5000000000000000 : ℝ) ^ (4495/1024 : ℝ) := by
    have hpowers : (100033640684699408299/100000000000000000000 : ℝ)^1024 ≤ (5000383132232781/5000000000000000 : ℝ)^4495 := by
      have hnat : (100033640684699408299 : ℕ)^1024*5000000000000000^4495 ≤ 5000383132232781^4495*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100033640684699408299 100000000000000000000 5000383132232781 5000000000000000 1024 4495 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000383132232781/5000000000000000 : ℝ)) (X := (100033640684699408299/100000000000000000000 : ℝ)) (by norm_num) 4495 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027765307842660259/50000000000000000000 : ℝ) ≤ (2500316212177587/2500000000000000 : ℝ) ^ (4495/1024 : ℝ) := by
    have hpowers : (50027765307842660259/50000000000000000000 : ℝ)^1024 ≤ (2500316212177587/2500000000000000 : ℝ)^4495 := by
      have hnat : (50027765307842660259 : ℕ)^1024*2500000000000000^4495 ≤ 2500316212177587^4495*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027765307842660259 50000000000000000000 2500316212177587 2500000000000000 1024 4495 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500316212177587/2500000000000000 : ℝ)) (X := (50027765307842660259/50000000000000000000 : ℝ)) (by norm_num) 4495 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(146884421418701/2500000000000000000 : ℝ) ≤ ((5765049697714221399/5766250000000000000 : ℝ)+2*(249292122393/230650000000000 : ℝ)*(2717/25000 : ℝ))^(4495/1024 : ℝ) := by
    rw [show (5765049697714221399/5766250000000000000 : ℝ)+2*(249292122393/230650000000000 : ℝ)*(2717/25000 : ℝ)=(1250033460027597/1250000000000000 : ℝ) by norm_num, show 1+2*(146884421418701/2500000000000000000 : ℝ)=(1250146884421418701/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27765307842660259/100000000000000000000 : ℝ)+(146884421418701/2500000000000000000 : ℝ) ≤ ((5765049697714221399/5766250000000000000 : ℝ)+(249292122393/230650000000000 : ℝ)*((15481/100000 : ℝ)+(2717/25000 : ℝ)))^(4495/1024 : ℝ) := by
    rw [show (5765049697714221399/5766250000000000000 : ℝ)+(249292122393/230650000000000 : ℝ)*((15481/100000 : ℝ)+(2717/25000 : ℝ))=(5000383132232781/5000000000000000 : ℝ) by norm_num, show 1+(27765307842660259/100000000000000000000 : ℝ)+(146884421418701/2500000000000000000 : ℝ)=(100033640684699408299/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27765307842660259/100000000000000000000 : ℝ) ≤ ((5765049697714221399/5766250000000000000 : ℝ)+2*(249292122393/230650000000000 : ℝ)*(15481/100000 : ℝ))^(4495/1024 : ℝ) := by
    rw [show (5765049697714221399/5766250000000000000 : ℝ)+2*(249292122393/230650000000000 : ℝ)*(15481/100000 : ℝ)=(2500316212177587/2500000000000000 : ℝ) by norm_num, show 1+2*(27765307842660259/100000000000000000000 : ℝ)=(50027765307842660259/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5765049697714221399/5766250000000000000 : ℝ)*(X 1 0+X 2 0)+(249292122393/230650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4495/1024 : ℝ)) (lo := (2717/25000 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (5765049697714221399/5766250000000000000 : ℝ)) (alpha := (249292122393/230650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5765049697714221399/5766250000000000000 : ℝ)*(X 0 1+X 2 1)+(249292122393/230650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4495/1024 : ℝ)) (lo := (2717/25000 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (5765049697714221399/5766250000000000000 : ℝ)) (alpha := (249292122393/230650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5765049697714221399/5766250000000000000 : ℝ)*(X 0 2+X 1 2)+(249292122393/230650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4495/1024 : ℝ)) (lo := (2717/25000 : ℝ)) (hi := (15481/100000 : ℝ)) (c := (5765049697714221399/5766250000000000000 : ℝ)) (alpha := (249292122393/230650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1885891609/10000000000 : ℝ)*X 0 0+(5434797817/10000000000 : ℝ)*X 0 1+(5217008157/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338062369/2500000000 : ℝ)*X 1 0+(-1997460117/10000000000 : ℝ)*X 1 1+(1304252049/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669031157/1250000000 : ℝ)*X 2 0+(1043401677/2000000000 : ℝ)*X 2 1+(-1997460159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2137696679/5000000000 : ℝ)*X 0 0+(2018282177/5000000000 : ℝ)*X 0 1+(4526247157/10000000000 : ℝ)*X 0 2+(2137696679/5000000000 : ℝ)*X 1 0+(2018282177/5000000000 : ℝ)*X 1 1+(4526247157/10000000000 : ℝ)*X 1 2+(2137696679/5000000000 : ℝ)*X 2 0+(2018282177/5000000000 : ℝ)*X 2 1+(4526247157/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-235740113/1250000000 : ℝ)*X 0 0+(5218126749/10000000000 : ℝ)*X 0 1+(2716835561/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295183007/10000000000 : ℝ)*X 1 0+(-1780797321/10000000000 : ℝ)*X 1 1+(5433671101/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647591497/5000000000 : ℝ)*X 2 0+(5433671139/10000000000 : ℝ)*X 2 1+(-890398643/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2137729849/5000000000 : ℝ)*X 0 0+(4523732631/10000000000 : ℝ)*X 0 1+(252443581/625000000 : ℝ)*X 0 2+(2137729849/5000000000 : ℝ)*X 1 0+(4523732631/10000000000 : ℝ)*X 1 1+(252443581/625000000 : ℝ)*X 1 2+(2137729849/5000000000 : ℝ)*X 2 0+(4523732631/10000000000 : ℝ)*X 2 1+(252443581/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17066155376986016451132603/4504882812500000000000000000000 : ℝ) := by norm_num
    linear_combination (90835951/10000000000000 : ℝ)*(base19) + (55718853/10000000000000 : ℝ)*(base23) + (1509179/800000000000 : ℝ)*(upper3) + (86939947/100000000000000 : ℝ)*(upper4) + (541651/20000000000000 : ℝ)*(upper5) + (829220453632997/25000000000000 : ℝ)*(major0) + (829220453632997/25000000000000 : ℝ)*(major1) + (829220453632997/25000000000000 : ℝ)*(major2) + (2295801534420899/50000000000000 : ℝ)*(sp0) + (2295807166365129/50000000000000 : ℝ)*(sp1) + (2295807341950619/50000000000000 : ℝ)*(sp2) + (10210711287369/500000000000 : ℝ)*(sp3) + (1217224797/10000000000000 : ℝ)*(sp4) + (1200844291/20000000000000 : ℝ)*(sp7) + (255268532711907/12500000000000 : ℝ)*(f.failure) + (573951905136221/12500000000000 : ℝ)*(f.sum) + (6384179941703/1441562500000000000000000000 : ℝ)*base65 + (2063103175732521553/144156250000000000000000000000000 : ℝ)*base67 + (1131823080314865303/144156250000000000000000000000000 : ℝ)*base69 + (584585068227490303/144156250000000000000000000000000 : ℝ)*base71 + (18284711725167/23065000000000000000000000000 : ℝ)*base74 + (1142991449988427803/144156250000000000000000000000000 : ℝ)*base75 + (1560071077741240303/144156250000000000000000000000000 : ℝ)*base77 + (1925985191165584053/144156250000000000000000000000000 : ℝ)*base79 + (10424925468549/11532500000000000000000000000 : ℝ)*base81 + (557587/250000000000000000000 : ℝ)*base89 + (557587/250000000000000000000 : ℝ)*base91 + (557587/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1256977793128705874992687563/144156250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1374007221/100000000000000 : ℝ)*(base19) + (183478191/12500000000000 : ℝ)*(base23) + (109187687/25000000000000 : ℝ)*(lower1) + (22615427/12500000000000 : ℝ)*(upper3) + (40381361/100000000000000 : ℝ)*(lower4) + (74271631/50000000000000 : ℝ)*(upper5) + (1675698153559421/50000000000000 : ℝ)*(major0) + (1675698153559421/50000000000000 : ℝ)*(major1) + (1675698153559421/50000000000000 : ℝ)*(major2) + (671515571/25000000000000 : ℝ)*(sp2) + (1159848517546859/25000000000000 : ℝ)*(sp4) + (927878539236043/20000000000000 : ℝ)*(sp5) + (37115119330397/800000000000 : ℝ)*(sp6) + (4030074713669/195312500000 : ℝ)*(sp7) + (4030074713669/195312500000 : ℝ)*(f.failure) + (1159848517546859/25000000000000 : ℝ)*(f.sum) + (29338500474547/5766250000000000000000000000 : ℝ)*base66 + (5531811479437175021/288312500000000000000000000000000 : ℝ)*base68 + (833692953030074979/288312500000000000000000000000000 : ℝ)*base69 + (16635832489207237521/288312500000000000000000000000000 : ℝ)*base72 + (4664443733867/23065000000000000000000000000 : ℝ)*base73 + (10863207342305137479/288312500000000000000000000000000 : ℝ)*base75 + (507335018652949979/288312500000000000000000000000000 : ℝ)*base77 + (2234188825121387479/288312500000000000000000000000000 : ℝ)*base79 + (79018681594009/11532500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (6151/976562500000000000 : ℝ)*base89 + (6151/976562500000000000 : ℝ)*base91 + (6151/976562500000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1500_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32484241/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2717/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10869/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (387/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1500_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1500_box_0 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-835046843/5000000000 : ℝ)*x 0 + (1080826477/2000000000 : ℝ)*x 1 + (5404130427/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (835046843/5000000000 : ℝ)^4497 ≤ (4926507154169/50000000000000 : ℝ)^3473 := by
    have hnat : (835046843 : ℕ)^4497*50000000000000^3473 ≤ 4926507154169^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835046843 5000000000 4926507154169 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080826477/2000000000 : ℝ)^4497 ≤ (22536751707773/50000000000000 : ℝ)^3473 := by
    have hnat : (1080826477 : ℕ)^4497*50000000000000^3473 ≤ 22536751707773^3473*2000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080826477 2000000000 22536751707773 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404130427/10000000000 : ℝ)^4497 ≤ (45073482269649/100000000000000 : ℝ)^3473 := by
    have hnat : (5404130427 : ℕ)^4497*100000000000000^3473 ≤ 45073482269649^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404130427 10000000000 45073482269649 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-835046843/5000000000 : ℝ), (1080826477/2000000000 : ℝ), (5404130427/10000000000 : ℝ)] ![(4926507154169/50000000000000 : ℝ), (22536751707773/50000000000000 : ℝ), (45073482269649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-835046843/5000000000 : ℝ)|^4497 ≤ (4926507154169/50000000000000 : ℝ)^3473
        have hw : |(-835046843/5000000000 : ℝ)|=(835046843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080826477/2000000000 : ℝ)|^4497 ≤ (22536751707773/50000000000000 : ℝ)^3473
        have hw : |(1080826477/2000000000 : ℝ)|=(1080826477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404130427/10000000000 : ℝ)|^4497 ≤ (45073482269649/100000000000000 : ℝ)^3473
        have hw : |(5404130427/10000000000 : ℝ)|=(5404130427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_box_1 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270604201/10000000000 : ℝ)*x 0 + (-463805921/2500000000 : ℝ)*x 1 + (5404131373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270604201/10000000000 : ℝ)^4497 ≤ (2181835850269/5000000000000 : ℝ)^3473 := by
    have hnat : (5270604201 : ℕ)^4497*5000000000000^3473 ≤ 2181835850269^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270604201 10000000000 2181835850269 5000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (463805921/2500000000 : ℝ)^4497 ≤ (11289790494169/100000000000000 : ℝ)^3473 := by
    have hnat : (463805921 : ℕ)^4497*100000000000000^3473 ≤ 11289790494169^3473*2500000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463805921 2500000000 11289790494169 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404131373/10000000000 : ℝ)^4497 ≤ (22536746243103/50000000000000 : ℝ)^3473 := by
    have hnat : (5404131373 : ℕ)^4497*50000000000000^3473 ≤ 22536746243103^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404131373 10000000000 22536746243103 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270604201/10000000000 : ℝ), (-463805921/2500000000 : ℝ), (5404131373/10000000000 : ℝ)] ![(2181835850269/5000000000000 : ℝ), (11289790494169/100000000000000 : ℝ), (22536746243103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270604201/10000000000 : ℝ)|^4497 ≤ (2181835850269/5000000000000 : ℝ)^3473
        have hw : |(5270604201/10000000000 : ℝ)|=(5270604201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-463805921/2500000000 : ℝ)|^4497 ≤ (11289790494169/100000000000000 : ℝ)^3473
        have hw : |(-463805921/2500000000 : ℝ)|=(463805921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404131373/10000000000 : ℝ)|^4497 ≤ (22536746243103/50000000000000 : ℝ)^3473
        have hw : |(5404131373/10000000000 : ℝ)|=(5404131373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_box_2 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635302097/5000000000 : ℝ)*x 0 + (2702065869/5000000000 : ℝ)*x 1 + (-1855223193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635302097/5000000000 : ℝ)^4497 ≤ (43636716930337/100000000000000 : ℝ)^3473 := by
    have hnat : (2635302097 : ℕ)^4497*100000000000000^3473 ≤ 43636716930337^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635302097 5000000000 43636716930337 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702065869/5000000000 : ℝ)^4497 ≤ (2817093526757/6250000000000 : ℝ)^3473 := by
    have hnat : (2702065869 : ℕ)^4497*6250000000000^3473 ≤ 2817093526757^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702065869 5000000000 2817093526757 6250000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1855223193/10000000000 : ℝ)^4497 ≤ (5644893312627/50000000000000 : ℝ)^3473 := by
    have hnat : (1855223193 : ℕ)^4497*50000000000000^3473 ≤ 5644893312627^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1855223193 10000000000 5644893312627 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635302097/5000000000 : ℝ), (2702065869/5000000000 : ℝ), (-1855223193/10000000000 : ℝ)] ![(43636716930337/100000000000000 : ℝ), (2817093526757/6250000000000 : ℝ), (5644893312627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635302097/5000000000 : ℝ)|^4497 ≤ (43636716930337/100000000000000 : ℝ)^3473
        have hw : |(2635302097/5000000000 : ℝ)|=(2635302097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702065869/5000000000 : ℝ)|^4497 ≤ (2817093526757/6250000000000 : ℝ)^3473
        have hw : |(2702065869/5000000000 : ℝ)|=(2702065869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1855223193/10000000000 : ℝ)|^4497 ≤ (5644893312627/50000000000000 : ℝ)^3473
        have hw : |(-1855223193/10000000000 : ℝ)|=(1855223193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_box_3 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4479013787/10000000000 : ℝ)*x 0 + (261290281/625000000 : ℝ)*x 1 + (261290261/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4479013787/10000000000 : ℝ)^4497 ≤ (17672783011141/50000000000000 : ℝ)^3473 := by
    have hnat : (4479013787 : ℕ)^4497*50000000000000^3473 ≤ 17672783011141^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479013787 10000000000 17672783011141 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261290281/625000000 : ℝ)^4497 ≤ (32327218582691/100000000000000 : ℝ)^3473 := by
    have hnat : (261290281 : ℕ)^4497*100000000000000^3473 ≤ 32327218582691^3473*625000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261290281 625000000 32327218582691 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261290261/625000000 : ℝ)^4497 ≤ (16163607689343/50000000000000 : ℝ)^3473 := by
    have hnat : (261290261 : ℕ)^4497*50000000000000^3473 ≤ 16163607689343^3473*625000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261290261 625000000 16163607689343 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4479013787/10000000000 : ℝ), (261290281/625000000 : ℝ), (261290261/625000000 : ℝ)] ![(17672783011141/50000000000000 : ℝ), (32327218582691/100000000000000 : ℝ), (16163607689343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4479013787/10000000000 : ℝ)|^4497 ≤ (17672783011141/50000000000000 : ℝ)^3473
        have hw : |(4479013787/10000000000 : ℝ)|=(4479013787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(261290281/625000000 : ℝ)|^4497 ≤ (32327218582691/100000000000000 : ℝ)^3473
        have hw : |(261290281/625000000 : ℝ)|=(261290281/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(261290261/625000000 : ℝ)|^4497 ≤ (16163607689343/50000000000000 : ℝ)^3473
        have hw : |(261290261/625000000 : ℝ)|=(261290261/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_box_4 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2107138789/10000000000 : ℝ)*x 0 + (5243216249/10000000000 : ℝ)*x 1 + (2621608141/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2107138789/10000000000 : ℝ)^4497 ≤ (208020830881/1562500000000 : ℝ)^3473 := by
    have hnat : (2107138789 : ℕ)^4497*1562500000000^3473 ≤ 208020830881^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107138789 10000000000 208020830881 1562500000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243216249/10000000000 : ℝ)^4497 ≤ (5417916653517/12500000000000 : ℝ)^3473 := by
    have hnat : (5243216249 : ℕ)^4497*12500000000000^3473 ≤ 5417916653517^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243216249 10000000000 5417916653517 12500000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621608141/5000000000 : ℝ)^4497 ≤ (8668666716273/20000000000000 : ℝ)^3473 := by
    have hnat : (2621608141 : ℕ)^4497*20000000000000^3473 ≤ 8668666716273^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621608141 5000000000 8668666716273 20000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2107138789/10000000000 : ℝ), (5243216249/10000000000 : ℝ), (2621608141/5000000000 : ℝ)] ![(208020830881/1562500000000 : ℝ), (5417916653517/12500000000000 : ℝ), (8668666716273/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2107138789/10000000000 : ℝ)|^4497 ≤ (208020830881/1562500000000 : ℝ)^3473
        have hw : |(-2107138789/10000000000 : ℝ)|=(2107138789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243216249/10000000000 : ℝ)|^4497 ≤ (5417916653517/12500000000000 : ℝ)^3473
        have hw : |(5243216249/10000000000 : ℝ)|=(5243216249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621608141/5000000000 : ℝ)|^4497 ≤ (8668666716273/20000000000000 : ℝ)^3473
        have hw : |(2621608141/5000000000 : ℝ)|=(2621608141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_box_5 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5382741441/10000000000 : ℝ)*x 0 + (-480352673/2500000000 : ℝ)*x 1 + (5243216521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5382741441/10000000000 : ℝ)^4497 ≤ (44842621639967/100000000000000 : ℝ)^3473 := by
    have hnat : (5382741441 : ℕ)^4497*100000000000000^3473 ≤ 44842621639967^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5382741441 10000000000 44842621639967 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (480352673/2500000000 : ℝ)^4497 ≤ (11814042206183/100000000000000 : ℝ)^3473 := by
    have hnat : (480352673 : ℕ)^4497*100000000000000^3473 ≤ 11814042206183^3473*2500000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480352673 2500000000 11814042206183 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243216521/10000000000 : ℝ)^4497 ≤ (43343336139601/100000000000000 : ℝ)^3473 := by
    have hnat : (5243216521 : ℕ)^4497*100000000000000^3473 ≤ 43343336139601^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243216521 10000000000 43343336139601 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5382741441/10000000000 : ℝ), (-480352673/2500000000 : ℝ), (5243216521/10000000000 : ℝ)] ![(44842621639967/100000000000000 : ℝ), (11814042206183/100000000000000 : ℝ), (43343336139601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5382741441/10000000000 : ℝ)|^4497 ≤ (44842621639967/100000000000000 : ℝ)^3473
        have hw : |(5382741441/10000000000 : ℝ)|=(5382741441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-480352673/2500000000 : ℝ)|^4497 ≤ (11814042206183/100000000000000 : ℝ)^3473
        have hw : |(-480352673/2500000000 : ℝ)|=(480352673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243216521/10000000000 : ℝ)|^4497 ≤ (43343336139601/100000000000000 : ℝ)^3473
        have hw : |(5243216521/10000000000 : ℝ)|=(5243216521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_box_6 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5382740999/10000000000 : ℝ)*x 0 + (262160813/500000000 : ℝ)*x 1 + (-960705821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5382740999/10000000000 : ℝ)^4497 ≤ (44842616872059/100000000000000 : ℝ)^3473 := by
    have hnat : (5382740999 : ℕ)^4497*100000000000000^3473 ≤ 44842616872059^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5382740999 10000000000 44842616872059 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262160813/500000000 : ℝ)^4497 ≤ (43343333345879/100000000000000 : ℝ)^3473 := by
    have hnat : (262160813 : ℕ)^4497*100000000000000^3473 ≤ 43343333345879^3473*500000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262160813 500000000 43343333345879 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (960705821/5000000000 : ℝ)^4497 ≤ (2362809953927/20000000000000 : ℝ)^3473 := by
    have hnat : (960705821 : ℕ)^4497*20000000000000^3473 ≤ 2362809953927^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      960705821 5000000000 2362809953927 20000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5382740999/10000000000 : ℝ), (262160813/500000000 : ℝ), (-960705821/5000000000 : ℝ)] ![(44842616872059/100000000000000 : ℝ), (43343333345879/100000000000000 : ℝ), (2362809953927/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5382740999/10000000000 : ℝ)|^4497 ≤ (44842616872059/100000000000000 : ℝ)^3473
        have hw : |(5382740999/10000000000 : ℝ)|=(5382740999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262160813/500000000 : ℝ)|^4497 ≤ (43343333345879/100000000000000 : ℝ)^3473
        have hw : |(262160813/500000000 : ℝ)|=(262160813/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-960705821/5000000000 : ℝ)|^4497 ≤ (2362809953927/20000000000000 : ℝ)^3473
        have hw : |(-960705821/5000000000 : ℝ)|=(960705821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_box_7 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2034706733/5000000000 : ℝ)*x 0 + (4385309449/10000000000 : ℝ)*x 1 + (438530779/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2034706733/5000000000 : ℝ)^4497 ≤ (31217912140029/100000000000000 : ℝ)^3473 := by
    have hnat : (2034706733 : ℕ)^4497*100000000000000^3473 ≤ 31217912140029^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2034706733 5000000000 31217912140029 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4385309449/10000000000 : ℝ)^4497 ≤ (17195526173121/50000000000000 : ℝ)^3473 := by
    have hnat : (4385309449 : ℕ)^4497*50000000000000^3473 ≤ 17195526173121^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4385309449 10000000000 17195526173121 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (438530779/1000000000 : ℝ)^4497 ≤ (17195517749871/50000000000000 : ℝ)^3473 := by
    have hnat : (438530779 : ℕ)^4497*50000000000000^3473 ≤ 17195517749871^3473*1000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438530779 1000000000 17195517749871 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2034706733/5000000000 : ℝ), (4385309449/10000000000 : ℝ), (438530779/1000000000 : ℝ)] ![(31217912140029/100000000000000 : ℝ), (17195526173121/50000000000000 : ℝ), (17195517749871/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2034706733/5000000000 : ℝ)|^4497 ≤ (31217912140029/100000000000000 : ℝ)^3473
        have hw : |(2034706733/5000000000 : ℝ)|=(2034706733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4385309449/10000000000 : ℝ)|^4497 ≤ (17195526173121/50000000000000 : ℝ)^3473
        have hw : |(4385309449/10000000000 : ℝ)|=(4385309449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(438530779/1000000000 : ℝ)|^4497 ≤ (17195517749871/50000000000000 : ℝ)^3473
        have hw : |(438530779/1000000000 : ℝ)|=(438530779/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_box_8 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2014846053/10000000000 : ℝ)*x 0 + (5130616399/10000000000 : ℝ)*x 1 + (67807749/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2014846053/10000000000 : ℝ)^4497 ≤ (12563203617161/100000000000000 : ℝ)^3473 := by
    have hnat : (2014846053 : ℕ)^4497*100000000000000^3473 ≤ 12563203617161^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014846053 10000000000 12563203617161 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5130616399/10000000000 : ℝ)^4497 ≤ (42141909274601/100000000000000 : ℝ)^3473 := by
    have hnat : (5130616399 : ℕ)^4497*100000000000000^3473 ≤ 42141909274601^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5130616399 10000000000 42141909274601 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67807749/125000000 : ℝ)^4497 ≤ (45294887089107/100000000000000 : ℝ)^3473 := by
    have hnat : (67807749 : ℕ)^4497*100000000000000^3473 ≤ 45294887089107^3473*125000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67807749 125000000 45294887089107 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2014846053/10000000000 : ℝ), (5130616399/10000000000 : ℝ), (67807749/125000000 : ℝ)] ![(12563203617161/100000000000000 : ℝ), (42141909274601/100000000000000 : ℝ), (45294887089107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2014846053/10000000000 : ℝ)|^4497 ≤ (12563203617161/100000000000000 : ℝ)^3473
        have hw : |(-2014846053/10000000000 : ℝ)|=(2014846053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5130616399/10000000000 : ℝ)|^4497 ≤ (42141909274601/100000000000000 : ℝ)^3473
        have hw : |(5130616399/10000000000 : ℝ)|=(5130616399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67807749/125000000 : ℝ)|^4497 ≤ (45294887089107/100000000000000 : ℝ)^3473
        have hw : |(67807749/125000000 : ℝ)|=(67807749/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_box_9 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328520037/625000000 : ℝ)*x 0 + (-11540917/62500000 : ℝ)*x 1 + (339038711/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328520037/625000000 : ℝ)^4497 ≤ (10870913162533/25000000000000 : ℝ)^3473 := by
    have hnat : (328520037 : ℕ)^4497*25000000000000^3473 ≤ 10870913162533^3473*625000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328520037 625000000 10870913162533 25000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11540917/62500000 : ℝ)^4497 ≤ (2805366531603/25000000000000 : ℝ)^3473 := by
    have hnat : (11540917 : ℕ)^4497*25000000000000^3473 ≤ 2805366531603^3473*62500000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11540917 62500000 2805366531603 25000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339038711/625000000 : ℝ)^4497 ≤ (45294881207489/100000000000000 : ℝ)^3473 := by
    have hnat : (339038711 : ℕ)^4497*100000000000000^3473 ≤ 45294881207489^3473*625000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339038711 625000000 45294881207489 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328520037/625000000 : ℝ), (-11540917/62500000 : ℝ), (339038711/625000000 : ℝ)] ![(10870913162533/25000000000000 : ℝ), (2805366531603/25000000000000 : ℝ), (45294881207489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328520037/625000000 : ℝ)|^4497 ≤ (10870913162533/25000000000000 : ℝ)^3473
        have hw : |(328520037/625000000 : ℝ)|=(328520037/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-11540917/62500000 : ℝ)|^4497 ≤ (2805366531603/25000000000000 : ℝ)^3473
        have hw : |(-11540917/62500000 : ℝ)|=(11540917/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339038711/625000000 : ℝ)|^4497 ≤ (45294881207489/100000000000000 : ℝ)^3473
        have hw : |(339038711/625000000 : ℝ)|=(339038711/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_box_10 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1314079793/2500000000 : ℝ)*x 0 + (5424621117/10000000000 : ℝ)*x 1 + (-1846546261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1314079793/2500000000 : ℝ)^4497 ≤ (43483637439383/100000000000000 : ℝ)^3473 := by
    have hnat : (1314079793 : ℕ)^4497*100000000000000^3473 ≤ 43483637439383^3473*2500000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314079793 2500000000 43483637439383 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424621117/10000000000 : ℝ)^4497 ≤ (45294900030831/100000000000000 : ℝ)^3473 := by
    have hnat : (5424621117 : ℕ)^4497*100000000000000^3473 ≤ 45294900030831^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424621117 10000000000 45294900030831 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1846546261/10000000000 : ℝ)^4497 ≤ (5610731257321/50000000000000 : ℝ)^3473 := by
    have hnat : (1846546261 : ℕ)^4497*50000000000000^3473 ≤ 5610731257321^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1846546261 10000000000 5610731257321 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1314079793/2500000000 : ℝ), (5424621117/10000000000 : ℝ), (-1846546261/10000000000 : ℝ)] ![(43483637439383/100000000000000 : ℝ), (45294900030831/100000000000000 : ℝ), (5610731257321/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1314079793/2500000000 : ℝ)|^4497 ≤ (43483637439383/100000000000000 : ℝ)^3473
        have hw : |(1314079793/2500000000 : ℝ)|=(1314079793/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424621117/10000000000 : ℝ)|^4497 ≤ (45294900030831/100000000000000 : ℝ)^3473
        have hw : |(5424621117/10000000000 : ℝ)|=(5424621117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1846546261/10000000000 : ℝ)|^4497 ≤ (5610731257321/50000000000000 : ℝ)^3473
        have hw : |(-1846546261/10000000000 : ℝ)|=(1846546261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_box_11 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4530012403/10000000000 : ℝ)*x 0 + (4154554281/10000000000 : ℝ)*x 1 + (830910673/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4530012403/10000000000 : ℝ)^4497 ≤ (35867547969593/100000000000000 : ℝ)^3473 := by
    have hnat : (4530012403 : ℕ)^4497*100000000000000^3473 ≤ 35867547969593^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4530012403 10000000000 35867547969593 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4154554281/10000000000 : ℝ)^4497 ≤ (8016557647147/25000000000000 : ℝ)^3473 := by
    have hnat : (4154554281 : ℕ)^4497*25000000000000^3473 ≤ 8016557647147^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4154554281 10000000000 8016557647147 25000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (830910673/2000000000 : ℝ)^4497 ≤ (32066221434037/100000000000000 : ℝ)^3473 := by
    have hnat : (830910673 : ℕ)^4497*100000000000000^3473 ≤ 32066221434037^3473*2000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830910673 2000000000 32066221434037 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4530012403/10000000000 : ℝ), (4154554281/10000000000 : ℝ), (830910673/2000000000 : ℝ)] ![(35867547969593/100000000000000 : ℝ), (8016557647147/25000000000000 : ℝ), (32066221434037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4530012403/10000000000 : ℝ)|^4497 ≤ (35867547969593/100000000000000 : ℝ)^3473
        have hw : |(4530012403/10000000000 : ℝ)|=(4530012403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4154554281/10000000000 : ℝ)|^4497 ≤ (8016557647147/25000000000000 : ℝ)^3473
        have hw : |(4154554281/10000000000 : ℝ)|=(4154554281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(830910673/2000000000 : ℝ)|^4497 ≤ (32066221434037/100000000000000 : ℝ)^3473
        have hw : |(830910673/2000000000 : ℝ)|=(830910673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_box_12 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-881200971/5000000000 : ℝ)*x 0 + (2756534957/5000000000 : ℝ)*x 1 + (2614100227/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (881200971/5000000000 : ℝ)^4497 ≤ (10563845985329/100000000000000 : ℝ)^3473 := by
    have hnat : (881200971 : ℕ)^4497*100000000000000^3473 ≤ 10563845985329^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881200971 5000000000 10563845985329 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2756534957/5000000000 : ℝ)^4497 ≤ (1156337016297/2500000000000 : ℝ)^3473 := by
    have hnat : (2756534957 : ℕ)^4497*2500000000000^3473 ≤ 1156337016297^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2756534957 5000000000 1156337016297 2500000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614100227/5000000000 : ℝ)^4497 ≤ (43182673343343/100000000000000 : ℝ)^3473 := by
    have hnat : (2614100227 : ℕ)^4497*100000000000000^3473 ≤ 43182673343343^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614100227 5000000000 43182673343343 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-881200971/5000000000 : ℝ), (2756534957/5000000000 : ℝ), (2614100227/5000000000 : ℝ)] ![(10563845985329/100000000000000 : ℝ), (1156337016297/2500000000000 : ℝ), (43182673343343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-881200971/5000000000 : ℝ)|^4497 ≤ (10563845985329/100000000000000 : ℝ)^3473
        have hw : |(-881200971/5000000000 : ℝ)|=(881200971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2756534957/5000000000 : ℝ)|^4497 ≤ (1156337016297/2500000000000 : ℝ)^3473
        have hw : |(2756534957/5000000000 : ℝ)|=(2756534957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614100227/5000000000 : ℝ)|^4497 ≤ (43182673343343/100000000000000 : ℝ)^3473
        have hw : |(2614100227/5000000000 : ℝ)|=(2614100227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_box_13 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (337075321/625000000 : ℝ)*x 0 + (-1927406363/10000000000 : ℝ)*x 1 + (1307050129/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (337075321/625000000 : ℝ)^4497 ≤ (44955527124267/100000000000000 : ℝ)^3473 := by
    have hnat : (337075321 : ℕ)^4497*100000000000000^3473 ≤ 44955527124267^3473*625000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337075321 625000000 44955527124267 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1927406363/10000000000 : ℝ)^4497 ≤ (5930899425517/50000000000000 : ℝ)^3473 := by
    have hnat : (1927406363 : ℕ)^4497*50000000000000^3473 ≤ 5930899425517^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1927406363 10000000000 5930899425517 50000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307050129/2500000000 : ℝ)^4497 ≤ (5397834250803/12500000000000 : ℝ)^3473 := by
    have hnat : (1307050129 : ℕ)^4497*12500000000000^3473 ≤ 5397834250803^3473*2500000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307050129 2500000000 5397834250803 12500000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(337075321/625000000 : ℝ), (-1927406363/10000000000 : ℝ), (1307050129/2500000000 : ℝ)] ![(44955527124267/100000000000000 : ℝ), (5930899425517/50000000000000 : ℝ), (5397834250803/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(337075321/625000000 : ℝ)|^4497 ≤ (44955527124267/100000000000000 : ℝ)^3473
        have hw : |(337075321/625000000 : ℝ)|=(337075321/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1927406363/10000000000 : ℝ)|^4497 ≤ (5930899425517/50000000000000 : ℝ)^3473
        have hw : |(-1927406363/10000000000 : ℝ)|=(1927406363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307050129/2500000000 : ℝ)|^4497 ≤ (5397834250803/12500000000000 : ℝ)^3473
        have hw : |(1307050129/2500000000 : ℝ)|=(1307050129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_box_14 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2696602653/5000000000 : ℝ)*x 0 + (5228200191/10000000000 : ℝ)*x 1 + (-192740657/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2696602653/5000000000 : ℝ)^4497 ≤ (5619441119891/12500000000000 : ℝ)^3473 := by
    have hnat : (2696602653 : ℕ)^4497*12500000000000^3473 ≤ 5619441119891^3473*5000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696602653 5000000000 5619441119891 12500000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5228200191/10000000000 : ℝ)^4497 ≤ (43182670530593/100000000000000 : ℝ)^3473 := by
    have hnat : (5228200191 : ℕ)^4497*100000000000000^3473 ≤ 43182670530593^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228200191 10000000000 43182670530593 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (192740657/1000000000 : ℝ)^4497 ≤ (2372360100117/20000000000000 : ℝ)^3473 := by
    have hnat : (192740657 : ℕ)^4497*20000000000000^3473 ≤ 2372360100117^3473*1000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192740657 1000000000 2372360100117 20000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2696602653/5000000000 : ℝ), (5228200191/10000000000 : ℝ), (-192740657/1000000000 : ℝ)] ![(5619441119891/12500000000000 : ℝ), (43182670530593/100000000000000 : ℝ), (2372360100117/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2696602653/5000000000 : ℝ)|^4497 ≤ (5619441119891/12500000000000 : ℝ)^3473
        have hw : |(2696602653/5000000000 : ℝ)|=(2696602653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5228200191/10000000000 : ℝ)|^4497 ≤ (43182670530593/100000000000000 : ℝ)^3473
        have hw : |(5228200191/10000000000 : ℝ)|=(5228200191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-192740657/1000000000 : ℝ)|^4497 ≤ (2372360100117/20000000000000 : ℝ)^3473
        have hw : |(-192740657/1000000000 : ℝ)|=(192740657/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1500_box_15 (p : ℝ) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4030331729/10000000000 : ℝ)*x 0 + (4404383917/10000000000 : ℝ)*x 1 + (1101096079/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4030331729/10000000000 : ℝ)^4497 ≤ (30830255448289/100000000000000 : ℝ)^3473 := by
    have hnat : (4030331729 : ℕ)^4497*100000000000000^3473 ≤ 30830255448289^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4030331729 10000000000 30830255448289 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4404383917/10000000000 : ℝ)^4497 ≤ (8646217560073/25000000000000 : ℝ)^3473 := by
    have hnat : (4404383917 : ℕ)^4497*25000000000000^3473 ≤ 8646217560073^3473*10000000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4404383917 10000000000 8646217560073 25000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1101096079/2500000000 : ℝ)^4497 ≤ (34584874297171/100000000000000 : ℝ)^3473 := by
    have hnat : (1101096079 : ℕ)^4497*100000000000000^3473 ≤ 34584874297171^3473*2500000000^4497 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1101096079 2500000000 34584874297171 100000000000000 4497 3473 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4497/1024 : ℝ)) 4497 3473 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4030331729/10000000000 : ℝ), (4404383917/10000000000 : ℝ), (1101096079/2500000000 : ℝ)] ![(30830255448289/100000000000000 : ℝ), (8646217560073/25000000000000 : ℝ), (34584874297171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4030331729/10000000000 : ℝ)|^4497 ≤ (30830255448289/100000000000000 : ℝ)^3473
        have hw : |(4030331729/10000000000 : ℝ)|=(4030331729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4404383917/10000000000 : ℝ)|^4497 ≤ (8646217560073/25000000000000 : ℝ)^3473
        have hw : |(4404383917/10000000000 : ℝ)|=(4404383917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1101096079/2500000000 : ℝ)|^4497 ≤ (34584874297171/100000000000000 : ℝ)^3473
        have hw : |(1101096079/2500000000 : ℝ)|=(1101096079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1500_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32484241/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10869/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15931/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58571/100000 : ℝ) ∧ (80189/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (21481/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (387/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10869/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (387/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10869/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (387/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10869/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (387/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10869/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (387/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10869/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (387/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10869/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10869/100000 : ℝ) ^ (4495/1024 : ℝ) ≤ (2938875162875273/50000000000000000000 : ℝ) := by
    have hpowers : (10869/100000 : ℝ)^4495 ≤ (2938875162875273/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10869 : ℕ)^4495*50000000000000000000^1024 ≤ 2938875162875273^1024*100000^4495 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10869 100000 2938875162875273 50000000000000000000 4495 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10869/100000 : ℝ)) (X := (2938875162875273/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4495 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (387/2500 : ℝ) ^ (4495/1024 : ℝ) ≤ (27757435831954253/100000000000000000000 : ℝ) := by
    have hpowers : (387/2500 : ℝ)^4495 ≤ (27757435831954253/100000000000000000000 : ℝ)^1024 := by
      have hnat : (387 : ℕ)^4495*100000000000000000000^1024 ≤ 27757435831954253^1024*2500^4495 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        387 2500 27757435831954253 100000000000000000000 4495 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (387/2500 : ℝ)) (X := (27757435831954253/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4495 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002938875162875273/25000000000000000000 : ℝ) ≤ (10000267788350329/10000000000000000 : ℝ) ^ (4495/1024 : ℝ) := by
    have hpowers : (25002938875162875273/25000000000000000000 : ℝ)^1024 ≤ (10000267788350329/10000000000000000 : ℝ)^4495 := by
      have hnat : (25002938875162875273 : ℕ)^1024*10000000000000000^4495 ≤ 10000267788350329^4495*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002938875162875273 25000000000000000000 10000267788350329 10000000000000000 1024 4495 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000267788350329/10000000000000000 : ℝ)) (X := (25002938875162875273/25000000000000000000 : ℝ)) (by norm_num) 4495 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100033635186157704799/100000000000000000000 : ℝ) ≤ (5000383069618269/5000000000000000 : ℝ) ^ (4495/1024 : ℝ) := by
    have hpowers : (100033635186157704799/100000000000000000000 : ℝ)^1024 ≤ (5000383069618269/5000000000000000 : ℝ)^4495 := by
      have hnat : (100033635186157704799 : ℕ)^1024*5000000000000000^4495 ≤ 5000383069618269^4495*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100033635186157704799 100000000000000000000 5000383069618269 5000000000000000 1024 4495 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000383069618269/5000000000000000 : ℝ)) (X := (100033635186157704799/100000000000000000000 : ℝ)) (by norm_num) 4495 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027757435831954253/50000000000000000000 : ℝ) ≤ (10001264490122747/10000000000000000 : ℝ) ^ (4495/1024 : ℝ) := by
    have hpowers : (50027757435831954253/50000000000000000000 : ℝ)^1024 ≤ (10001264490122747/10000000000000000 : ℝ)^4495 := by
      have hnat : (50027757435831954253 : ℕ)^1024*10000000000000000^4495 ≤ 10001264490122747^4495*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027757435831954253 50000000000000000000 10001264490122747 10000000000000000 1024 4495 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001264490122747/10000000000000000 : ℝ)) (X := (50027757435831954253/50000000000000000000 : ℝ)) (by norm_num) 4495 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2938875162875273/50000000000000000000 : ℝ) ≤ ((15366800540172985259/15370000000000000000 : ℝ)+2*(498350886209/461100000000000 : ℝ)*(10869/100000 : ℝ))^(4495/1024 : ℝ) := by
    rw [show (15366800540172985259/15370000000000000000 : ℝ)+2*(498350886209/461100000000000 : ℝ)*(10869/100000 : ℝ)=(10000267788350329/10000000000000000 : ℝ) by norm_num, show 1+2*(2938875162875273/50000000000000000000 : ℝ)=(25002938875162875273/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27757435831954253/100000000000000000000 : ℝ)+(2938875162875273/50000000000000000000 : ℝ) ≤ ((15366800540172985259/15370000000000000000 : ℝ)+(498350886209/461100000000000 : ℝ)*((387/2500 : ℝ)+(10869/100000 : ℝ)))^(4495/1024 : ℝ) := by
    rw [show (15366800540172985259/15370000000000000000 : ℝ)+(498350886209/461100000000000 : ℝ)*((387/2500 : ℝ)+(10869/100000 : ℝ))=(5000383069618269/5000000000000000 : ℝ) by norm_num, show 1+(27757435831954253/100000000000000000000 : ℝ)+(2938875162875273/50000000000000000000 : ℝ)=(100033635186157704799/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27757435831954253/100000000000000000000 : ℝ) ≤ ((15366800540172985259/15370000000000000000 : ℝ)+2*(498350886209/461100000000000 : ℝ)*(387/2500 : ℝ))^(4495/1024 : ℝ) := by
    rw [show (15366800540172985259/15370000000000000000 : ℝ)+2*(498350886209/461100000000000 : ℝ)*(387/2500 : ℝ)=(10001264490122747/10000000000000000 : ℝ) by norm_num, show 1+2*(27757435831954253/100000000000000000000 : ℝ)=(50027757435831954253/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15366800540172985259/15370000000000000000 : ℝ)*(X 1 0+X 2 0)+(498350886209/461100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4495/1024 : ℝ)) (lo := (10869/100000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (15366800540172985259/15370000000000000000 : ℝ)) (alpha := (498350886209/461100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15366800540172985259/15370000000000000000 : ℝ)*(X 0 1+X 2 1)+(498350886209/461100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4495/1024 : ℝ)) (lo := (10869/100000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (15366800540172985259/15370000000000000000 : ℝ)) (alpha := (498350886209/461100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15366800540172985259/15370000000000000000 : ℝ)*(X 0 2+X 1 2)+(498350886209/461100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4495/1024 : ℝ)) (lo := (10869/100000 : ℝ)) (hi := (387/2500 : ℝ)) (c := (15366800540172985259/15370000000000000000 : ℝ)) (alpha := (498350886209/461100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-835046843/5000000000 : ℝ)*X 0 0+(1080826477/2000000000 : ℝ)*X 0 1+(5404130427/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5270604201/10000000000 : ℝ)*X 1 0+(-463805921/2500000000 : ℝ)*X 1 1+(5404131373/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2635302097/5000000000 : ℝ)*X 2 0+(2702065869/5000000000 : ℝ)*X 2 1+(-1855223193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4479013787/10000000000 : ℝ)*X 0 0+(261290281/625000000 : ℝ)*X 0 1+(261290261/625000000 : ℝ)*X 0 2+(4479013787/10000000000 : ℝ)*X 1 0+(261290281/625000000 : ℝ)*X 1 1+(261290261/625000000 : ℝ)*X 1 2+(4479013787/10000000000 : ℝ)*X 2 0+(261290281/625000000 : ℝ)*X 2 1+(261290261/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2107138789/10000000000 : ℝ)*X 0 0+(5243216249/10000000000 : ℝ)*X 0 1+(2621608141/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5382741441/10000000000 : ℝ)*X 1 0+(-480352673/2500000000 : ℝ)*X 1 1+(5243216521/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5382740999/10000000000 : ℝ)*X 2 0+(262160813/500000000 : ℝ)*X 2 1+(-960705821/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2034706733/5000000000 : ℝ)*X 0 0+(4385309449/10000000000 : ℝ)*X 0 1+(438530779/1000000000 : ℝ)*X 0 2+(2034706733/5000000000 : ℝ)*X 1 0+(4385309449/10000000000 : ℝ)*X 1 1+(438530779/1000000000 : ℝ)*X 1 2+(2034706733/5000000000 : ℝ)*X 2 0+(4385309449/10000000000 : ℝ)*X 2 1+(438530779/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2014846053/10000000000 : ℝ)*X 0 0+(5130616399/10000000000 : ℝ)*X 0 1+(67807749/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((328520037/625000000 : ℝ)*X 1 0+(-11540917/62500000 : ℝ)*X 1 1+(339038711/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1314079793/2500000000 : ℝ)*X 2 0+(5424621117/10000000000 : ℝ)*X 2 1+(-1846546261/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4530012403/10000000000 : ℝ)*X 0 0+(4154554281/10000000000 : ℝ)*X 0 1+(830910673/2000000000 : ℝ)*X 0 2+(4530012403/10000000000 : ℝ)*X 1 0+(4154554281/10000000000 : ℝ)*X 1 1+(830910673/2000000000 : ℝ)*X 1 2+(4530012403/10000000000 : ℝ)*X 2 0+(4154554281/10000000000 : ℝ)*X 2 1+(830910673/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-881200971/5000000000 : ℝ)*X 0 0+(2756534957/5000000000 : ℝ)*X 0 1+(2614100227/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((337075321/625000000 : ℝ)*X 1 0+(-1927406363/10000000000 : ℝ)*X 1 1+(1307050129/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2696602653/5000000000 : ℝ)*X 2 0+(5228200191/10000000000 : ℝ)*X 2 1+(-192740657/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4030331729/10000000000 : ℝ)*X 0 0+(4404383917/10000000000 : ℝ)*X 0 1+(1101096079/2500000000 : ℝ)*X 0 2+(4030331729/10000000000 : ℝ)*X 1 0+(4404383917/10000000000 : ℝ)*X 1 1+(1101096079/2500000000 : ℝ)*X 1 2+(4030331729/10000000000 : ℝ)*X 2 0+(4404383917/10000000000 : ℝ)*X 2 1+(1101096079/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1500_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15931/25000 : ℝ) ≤ (-244850810677184882020654923238231/384250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (141644909/50000000000000 : ℝ)*(upper1) + (71531631/50000000000000 : ℝ)*(upper2) + (154771759/100000000000000 : ℝ)*(upper3) + (32808637/25000000000000 : ℝ)*(lower4) + (1102814306248297/50000000000000 : ℝ)*(major0) + (1102814306248297/50000000000000 : ℝ)*(major1) + (1102814306248297/50000000000000 : ℝ)*(major2) + (948942809/25000000000000 : ℝ)*(sp3) + (1537264711666159/50000000000000 : ℝ)*(sp4) + (1537197450328091/50000000000000 : ℝ)*(sp5) + (3074527171090201/100000000000000 : ℝ)*(sp6) + (1357964588034681/100000000000000 : ℝ)*(sp7) + (16815334517/12500000000000 : ℝ)*(sp13) + (1126121059/50000000000000 : ℝ)*(sp14) + (339492095951479/25000000000000 : ℝ)*(f.failure) + (1537264711666159/50000000000000 : ℝ)*(f.sum) + (6699260447767/11527500000000000000000000000 : ℝ)*base66 + (4209137986893361769/2305500000000000000000000000000000 : ℝ)*base67 + (82253648555179138231/2305500000000000000000000000000000 : ℝ)*base70 + (9058011226366138231/2305500000000000000000000000000000 : ℝ)*base72 + (100518854885069/23055000000000000000000000000 : ℝ)*base74 + (45229279833949861769/2305500000000000000000000000000000 : ℝ)*base75 + (8043720677885638231/2305500000000000000000000000000000 : ℝ)*base78 + (9280982556794638231/2305500000000000000000000000000000 : ℝ)*base80 + (379157270198587/11527500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1857561/500000000000000000000 : ℝ)*base90 + (1857561/500000000000000000000 : ℝ)*base92 + (1857561/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (58571/100000 : ℝ) ≤ (14066848109596219089432029399181/24015625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (79160943/50000000000000 : ℝ)*(upper0) + (36504859/20000000000000 : ℝ)*(upper3) + (223716769/100000000000000 : ℝ)*(upper4) + (71283381562661/3125000000000 : ℝ)*(major0) + (71283381562661/3125000000000 : ℝ)*(major1) + (71283381562661/3125000000000 : ℝ)*(major2) + (3138180132157277/100000000000000 : ℝ)*(sp0) + (392273944472787/12500000000000 : ℝ)*(sp1) + (1569085704761069/50000000000000 : ℝ)*(sp2) + (1404408707668779/100000000000000 : ℝ)*(sp3) + (5013257621/100000000000000 : ℝ)*(sp5) + (25159517779/100000000000000 : ℝ)*(sp6) + (1313114823/20000000000000 : ℝ)*(sp7) + (205461033/1250000000000 : ℝ)*(sp8) + (702207636621447/50000000000000 : ℝ)*(f.failure) + (3138196569039917/100000000000000 : ℝ)*(f.sum) + (62257775301113/23055000000000000000000000000 : ℝ)*base65 + (815200849220092597/144093750000000000000000000000000 : ℝ)*base67 + (1799885517579498847/144093750000000000000000000000000 : ℝ)*base69 + (1636383349983967597/144093750000000000000000000000000 : ℝ)*base71 + (86264957825497/23055000000000000000000000000 : ℝ)*base74 + (1166366845592936347/144093750000000000000000000000000 : ℝ)*base75 + (1626790937402842597/144093750000000000000000000000000 : ℝ)*base77 + (945592121110188653/144093750000000000000000000000000 : ℝ)*base80 + (77394607103329/11527500000000000000000000000 : ℝ)*base81 + (9883273/1000000000000000000000 : ℝ)*base90 + (9883273/1000000000000000000000 : ℝ)*base92 + (9883273/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80189/100000 : ℝ) ≤ (154068458466421045087408800514197/192125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (169636151/100000000000000 : ℝ)*(upper1) + (105705121/100000000000000 : ℝ)*(upper2) + (21532937/50000000000000 : ℝ)*(lower5) + (619087729513461/25000000000000 : ℝ)*(major0) + (619087729513461/25000000000000 : ℝ)*(major1) + (619087729513461/25000000000000 : ℝ)*(major2) + (4142033717/100000000000000 : ℝ)*(sp1) + (67063103413/25000000000000 : ℝ)*(sp2) + (7126982173/25000000000000 : ℝ)*(sp3) + (1316514763/100000000000000 : ℝ)*(sp4) + (1700661189465051/50000000000000 : ℝ)*(sp8) + (850329888352787/25000000000000 : ℝ)*(sp9) + (850263860757803/25000000000000 : ℝ)*(sp10) + (762309519601379/50000000000000 : ℝ)*(sp11) + (30492950942629/2000000000000 : ℝ)*(f.failure) + (26572841370663/781250000000 : ℝ)*(f.sum) + (17549581421393/7685000000000000000000000000 : ℝ)*base66 + (5221031347615378601/384250000000000000000000000000000 : ℝ)*base68 + (2514977064105628601/384250000000000000000000000000000 : ℝ)*base70 + (970909685653378601/384250000000000000000000000000000 : ℝ)*base72 + (25388775405319/3842500000000000000000000000 : ℝ)*base74 + (2116425042001621399/384250000000000000000000000000000 : ℝ)*base75 + (89228163804128601/384250000000000000000000000000000 : ℝ)*base78 + (858931697030871399/384250000000000000000000000000000 : ℝ)*base79 + (9333011177371/3842500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (9589/40000000000000000000 : ℝ)*base89 + (9589/40000000000000000000 : ℝ)*base91 + (9589/40000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-21481/25000 : ℝ) ≤ (-20634672383077308141826414363731/24015625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3379877/12500000000000 : ℝ)*(lower0) + (1698147/2500000000000 : ℝ)*(lower1) + (713197/20000000000000 : ℝ)*(lower3) + (3691763/10000000000000 : ℝ)*(lower4) + (78597914796289/3125000000000 : ℝ)*(major0) + (78597914796289/3125000000000 : ℝ)*(major1) + (78597914796289/3125000000000 : ℝ)*(major2) + (28366751177/100000000000000 : ℝ)*(sp5) + (60336640521/50000000000000 : ℝ)*(sp6) + (3296816507/20000000000000 : ℝ)*(sp7) + (877595494457087/25000000000000 : ℝ)*(sp12) + (351035361107717/10000000000000 : ℝ)*(sp13) + (1755130652273653/50000000000000 : ℝ)*(sp14) + (387127176503179/25000000000000 : ℝ)*(sp15) + (1548525190095251/100000000000000 : ℝ)*(f.failure) + (877595494457087/25000000000000 : ℝ)*(f.sum) + (49116903549821/11527500000000000000000000000 : ℝ)*base65 + (6190269737030303/144093750000000000000000000000000 : ℝ)*base67 + (2010650177992374053/144093750000000000000000000000000 : ℝ)*base69 + (2709681588839780303/144093750000000000000000000000000 : ℝ)*base71 + (117261603782783/23055000000000000000000000000 : ℝ)*base74 + (1303907086073780303/144093750000000000000000000000000 : ℝ)*base75 + (611636902971436553/144093750000000000000000000000000 : ℝ)*base77 + (130231395001532197/144093750000000000000000000000000 : ℝ)*base80 + (65374274392061/11527500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (13560509/2000000000000000000000 : ℝ)*base90 + (13560509/2000000000000000000000 : ℝ)*base92 + (13560509/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1500_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32484241/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (387/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10869/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15931/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58571/100000 : ℝ) else (80189/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21481/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1500_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1500_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32484241/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2717/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15931/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58571/100000 : ℝ) else (80189/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21481/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1500_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1500_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4495/1024 : ℝ) ≤ p) (hpb : p ≤ (4497/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (32484241/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2717/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15931/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58571/100000 : ℝ) else (80189/100000 : ℝ) ≤ X j i ∧ X j i ≤ (21481/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1500_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
