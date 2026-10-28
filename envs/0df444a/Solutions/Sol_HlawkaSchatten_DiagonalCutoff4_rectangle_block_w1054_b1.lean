-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1054_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:58:05.4446+00:00
-- url     : https://prove2.me/submissions/f13632eb-46a2-4c2a-97fe-6b9ffe89fc17

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
theorem support_rectangle_w1054_s3_0 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2204781509/10000000000 : ℝ)*x 0 + (1087790581/2000000000 : ℝ)*x 1 + (5223052879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2204781509/10000000000 : ℝ)^8247 ≤ (2675835310527/20000000000000 : ℝ)^6199 := by
    have hnat : (2204781509 : ℕ)^8247*20000000000000^6199 ≤ 2675835310527^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204781509 10000000000 2675835310527 20000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087790581/2000000000 : ℝ)^8247 ≤ (22238523020621/50000000000000 : ℝ)^6199 := by
    have hnat : (1087790581 : ℕ)^8247*50000000000000^6199 ≤ 22238523020621^6199*2000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087790581 2000000000 22238523020621 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5223052879/10000000000 : ℝ)^8247 ≤ (8428755478471/20000000000000 : ℝ)^6199 := by
    have hnat : (5223052879 : ℕ)^8247*20000000000000^6199 ≤ 8428755478471^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223052879 10000000000 8428755478471 20000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2204781509/10000000000 : ℝ), (1087790581/2000000000 : ℝ), (5223052879/10000000000 : ℝ)] ![(2675835310527/20000000000000 : ℝ), (22238523020621/50000000000000 : ℝ), (8428755478471/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2204781509/10000000000 : ℝ)|^8247 ≤ (2675835310527/20000000000000 : ℝ)^6199
        have hw : |(-2204781509/10000000000 : ℝ)|=(2204781509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087790581/2000000000 : ℝ)|^8247 ≤ (22238523020621/50000000000000 : ℝ)^6199
        have hw : |(1087790581/2000000000 : ℝ)|=(1087790581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5223052879/10000000000 : ℝ)|^8247 ≤ (8428755478471/20000000000000 : ℝ)^6199
        have hw : |(5223052879/10000000000 : ℝ)|=(5223052879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s3_1 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5356004259/10000000000 : ℝ)*x 0 + (-1157686659/5000000000 : ℝ)*x 1 + (5223052763/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356004259/10000000000 : ℝ)^8247 ≤ (43576916407717/100000000000000 : ℝ)^6199 := by
    have hnat : (5356004259 : ℕ)^8247*100000000000000^6199 ≤ 43576916407717^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356004259 10000000000 43576916407717 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1157686659/5000000000 : ℝ)^8247 ≤ (713965371917/5000000000000 : ℝ)^6199 := by
    have hnat : (1157686659 : ℕ)^8247*5000000000000^6199 ≤ 713965371917^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1157686659 5000000000 713965371917 5000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5223052763/10000000000 : ℝ)^8247 ≤ (10535944036787/25000000000000 : ℝ)^6199 := by
    have hnat : (5223052763 : ℕ)^8247*25000000000000^6199 ≤ 10535944036787^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223052763 10000000000 10535944036787 25000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356004259/10000000000 : ℝ), (-1157686659/5000000000 : ℝ), (5223052763/10000000000 : ℝ)] ![(43576916407717/100000000000000 : ℝ), (713965371917/5000000000000 : ℝ), (10535944036787/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356004259/10000000000 : ℝ)|^8247 ≤ (43576916407717/100000000000000 : ℝ)^6199
        have hw : |(5356004259/10000000000 : ℝ)|=(5356004259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1157686659/5000000000 : ℝ)|^8247 ≤ (713965371917/5000000000000 : ℝ)^6199
        have hw : |(-1157686659/5000000000 : ℝ)|=(1157686659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5223052763/10000000000 : ℝ)|^8247 ≤ (10535944036787/25000000000000 : ℝ)^6199
        have hw : |(5223052763/10000000000 : ℝ)|=(5223052763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s3_2 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5356004171/10000000000 : ℝ)*x 0 + (522305261/1000000000 : ℝ)*x 1 + (-2315373633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5356004171/10000000000 : ℝ)^8247 ≤ (54471144319/125000000000 : ℝ)^6199 := by
    have hnat : (5356004171 : ℕ)^8247*125000000000^6199 ≤ 54471144319^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5356004171 10000000000 54471144319 125000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (522305261/1000000000 : ℝ)^8247 ≤ (10535943626191/25000000000000 : ℝ)^6199 := by
    have hnat : (522305261 : ℕ)^8247*25000000000000^6199 ≤ 10535943626191^6199*1000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522305261 1000000000 10535943626191 25000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2315373633/10000000000 : ℝ)^8247 ≤ (14279310022807/100000000000000 : ℝ)^6199 := by
    have hnat : (2315373633 : ℕ)^8247*100000000000000^6199 ≤ 14279310022807^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2315373633 10000000000 14279310022807 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5356004171/10000000000 : ℝ), (522305261/1000000000 : ℝ), (-2315373633/10000000000 : ℝ)] ![(54471144319/125000000000 : ℝ), (10535943626191/25000000000000 : ℝ), (14279310022807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5356004171/10000000000 : ℝ)|^8247 ≤ (54471144319/125000000000 : ℝ)^6199
        have hw : |(5356004171/10000000000 : ℝ)|=(5356004171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(522305261/1000000000 : ℝ)|^8247 ≤ (10535943626191/25000000000000 : ℝ)^6199
        have hw : |(522305261/1000000000 : ℝ)|=(522305261/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2315373633/10000000000 : ℝ)|^8247 ≤ (14279310022807/100000000000000 : ℝ)^6199
        have hw : |(-2315373633/10000000000 : ℝ)|=(2315373633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s3_3 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2187160531/5000000000 : ℝ)*x 0 + (4168422611/10000000000 : ℝ)*x 1 + (573818739/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187160531/5000000000 : ℝ)^8247 ≤ (33287118519207/100000000000000 : ℝ)^6199 := by
    have hnat : (2187160531 : ℕ)^8247*100000000000000^6199 ≤ 33287118519207^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187160531 5000000000 33287118519207 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4168422611/10000000000 : ℝ)^8247 ≤ (31219042437137/100000000000000 : ℝ)^6199 := by
    have hnat : (4168422611 : ℕ)^8247*100000000000000^6199 ≤ 31219042437137^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4168422611 10000000000 31219042437137 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (573818739/1250000000 : ℝ)^8247 ≤ (35493839027631/100000000000000 : ℝ)^6199 := by
    have hnat : (573818739 : ℕ)^8247*100000000000000^6199 ≤ 35493839027631^6199*1250000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      573818739 1250000000 35493839027631 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187160531/5000000000 : ℝ), (4168422611/10000000000 : ℝ), (573818739/1250000000 : ℝ)] ![(33287118519207/100000000000000 : ℝ), (31219042437137/100000000000000 : ℝ), (35493839027631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187160531/5000000000 : ℝ)|^8247 ≤ (33287118519207/100000000000000 : ℝ)^6199
        have hw : |(2187160531/5000000000 : ℝ)|=(2187160531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4168422611/10000000000 : ℝ)|^8247 ≤ (31219042437137/100000000000000 : ℝ)^6199
        have hw : |(4168422611/10000000000 : ℝ)|=(4168422611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(573818739/1250000000 : ℝ)|^8247 ≤ (35493839027631/100000000000000 : ℝ)^6199
        have hw : |(573818739/1250000000 : ℝ)|=(573818739/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s3_4 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-34450071/156250000 : ℝ)*x 0 + (5223945001/10000000000 : ℝ)*x 1 + (2719027749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34450071/156250000 : ℝ)^8247 ≤ (2675872503179/20000000000000 : ℝ)^6199 := by
    have hnat : (34450071 : ℕ)^8247*20000000000000^6199 ≤ 2675872503179^6199*156250000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34450071 156250000 2675872503179 20000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5223945001/10000000000 : ℝ)^8247 ≤ (5269169272609/12500000000000 : ℝ)^6199 := by
    have hnat : (5223945001 : ℕ)^8247*12500000000000^6199 ≤ 5269169272609^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223945001 10000000000 5269169272609 12500000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719027749/5000000000 : ℝ)^8247 ≤ (44467283281291/100000000000000 : ℝ)^6199 := by
    have hnat : (2719027749 : ℕ)^8247*100000000000000^6199 ≤ 44467283281291^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719027749 5000000000 44467283281291 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-34450071/156250000 : ℝ), (5223945001/10000000000 : ℝ), (2719027749/5000000000 : ℝ)] ![(2675872503179/20000000000000 : ℝ), (5269169272609/12500000000000 : ℝ), (44467283281291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-34450071/156250000 : ℝ)|^8247 ≤ (2675872503179/20000000000000 : ℝ)^6199
        have hw : |(-34450071/156250000 : ℝ)|=(34450071/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5223945001/10000000000 : ℝ)|^8247 ≤ (5269169272609/12500000000000 : ℝ)^6199
        have hw : |(5223945001/10000000000 : ℝ)|=(5223945001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719027749/5000000000 : ℝ)|^8247 ≤ (44467283281291/100000000000000 : ℝ)^6199
        have hw : |(2719027749/5000000000 : ℝ)|=(2719027749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s3_5 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1325417627/2500000000 : ℝ)*x 0 + (-2100371191/10000000000 : ℝ)*x 1 + (5438054877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325417627/2500000000 : ℝ)^8247 ≤ (335857755709/781250000000 : ℝ)^6199 := by
    have hnat : (1325417627 : ℕ)^8247*781250000000^6199 ≤ 335857755709^6199*2500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325417627 2500000000 335857755709 781250000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2100371191/10000000000 : ℝ)^8247 ≤ (12542930724441/100000000000000 : ℝ)^6199 := by
    have hnat : (2100371191 : ℕ)^8247*100000000000000^6199 ≤ 12542930724441^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100371191 10000000000 12542930724441 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5438054877/10000000000 : ℝ)^8247 ≤ (44467276525707/100000000000000 : ℝ)^6199 := by
    have hnat : (5438054877 : ℕ)^8247*100000000000000^6199 ≤ 44467276525707^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438054877 10000000000 44467276525707 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325417627/2500000000 : ℝ), (-2100371191/10000000000 : ℝ), (5438054877/10000000000 : ℝ)] ![(335857755709/781250000000 : ℝ), (12542930724441/100000000000000 : ℝ), (44467276525707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325417627/2500000000 : ℝ)|^8247 ≤ (335857755709/781250000000 : ℝ)^6199
        have hw : |(1325417627/2500000000 : ℝ)|=(1325417627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2100371191/10000000000 : ℝ)|^8247 ≤ (12542930724441/100000000000000 : ℝ)^6199
        have hw : |(-2100371191/10000000000 : ℝ)|=(2100371191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5438054877/10000000000 : ℝ)|^8247 ≤ (44467276525707/100000000000000 : ℝ)^6199
        have hw : |(5438054877/10000000000 : ℝ)|=(5438054877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s3_6 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5301670199/10000000000 : ℝ)*x 0 + (5438055339/10000000000 : ℝ)*x 1 + (-2100370979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301670199/10000000000 : ℝ)^8247 ≤ (42989789397367/100000000000000 : ℝ)^6199 := by
    have hnat : (5301670199 : ℕ)^8247*100000000000000^6199 ≤ 42989789397367^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301670199 10000000000 42989789397367 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438055339/10000000000 : ℝ)^8247 ≤ (111168203879/250000000000 : ℝ)^6199 := by
    have hnat : (5438055339 : ℕ)^8247*250000000000^6199 ≤ 111168203879^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438055339 10000000000 111168203879 250000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2100370979/10000000000 : ℝ)^8247 ≤ (6271464520083/50000000000000 : ℝ)^6199 := by
    have hnat : (2100370979 : ℕ)^8247*50000000000000^6199 ≤ 6271464520083^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100370979 10000000000 6271464520083 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301670199/10000000000 : ℝ), (5438055339/10000000000 : ℝ), (-2100370979/10000000000 : ℝ)] ![(42989789397367/100000000000000 : ℝ), (111168203879/250000000000 : ℝ), (6271464520083/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301670199/10000000000 : ℝ)|^8247 ≤ (42989789397367/100000000000000 : ℝ)^6199
        have hw : |(5301670199/10000000000 : ℝ)|=(5301670199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438055339/10000000000 : ℝ)|^8247 ≤ (111168203879/250000000000 : ℝ)^6199
        have hw : |(5438055339/10000000000 : ℝ)|=(5438055339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2100370979/10000000000 : ℝ)|^8247 ≤ (6271464520083/50000000000000 : ℝ)^6199
        have hw : |(-2100370979/10000000000 : ℝ)|=(2100370979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s3_7 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4374366221/10000000000 : ℝ)*x 0 + (2294402117/5000000000 : ℝ)*x 1 + (2085089349/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374366221/10000000000 : ℝ)^8247 ≤ (16643787848413/50000000000000 : ℝ)^6199 := by
    have hnat : (4374366221 : ℕ)^8247*50000000000000^6199 ≤ 16643787848413^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374366221 10000000000 16643787848413 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2294402117/5000000000 : ℝ)^8247 ≤ (35475883446141/100000000000000 : ℝ)^6199 := by
    have hnat : (2294402117 : ℕ)^8247*100000000000000^6199 ≤ 35475883446141^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2294402117 5000000000 35475883446141 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085089349/5000000000 : ℝ)^8247 ≤ (31236540841179/100000000000000 : ℝ)^6199 := by
    have hnat : (2085089349 : ℕ)^8247*100000000000000^6199 ≤ 31236540841179^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085089349 5000000000 31236540841179 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374366221/10000000000 : ℝ), (2294402117/5000000000 : ℝ), (2085089349/5000000000 : ℝ)] ![(16643787848413/50000000000000 : ℝ), (35475883446141/100000000000000 : ℝ), (31236540841179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374366221/10000000000 : ℝ)|^8247 ≤ (16643787848413/50000000000000 : ℝ)^6199
        have hw : |(4374366221/10000000000 : ℝ)|=(4374366221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2294402117/5000000000 : ℝ)|^8247 ≤ (35475883446141/100000000000000 : ℝ)^6199
        have hw : |(2294402117/5000000000 : ℝ)|=(2294402117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2085089349/5000000000 : ℝ)|^8247 ≤ (31236540841179/100000000000000 : ℝ)^6199
        have hw : |(2085089349/5000000000 : ℝ)|=(2085089349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1054_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16781/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8653/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2589/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3731/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16781/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8653/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16781/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8653/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16781/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8653/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16781/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8653/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16781/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8653/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16781/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8653/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8653/100000 : ℝ) ^ (4123/1024 : ℝ) ≤ (2627924563901701/50000000000000000000 : ℝ) := by
    have hpowers : (8653/100000 : ℝ)^4123 ≤ (2627924563901701/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8653 : ℕ)^4123*50000000000000000000^1024 ≤ 2627924563901701^1024*100000^4123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8653 100000 2627924563901701 50000000000000000000 4123 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8653/100000 : ℝ)) (X := (2627924563901701/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16781/100000 : ℝ) ^ (4123/1024 : ℝ) ≤ (37827007058867883/50000000000000000000 : ℝ) := by
    have hpowers : (16781/100000 : ℝ)^4123 ≤ (37827007058867883/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16781 : ℕ)^4123*50000000000000000000^1024 ≤ 37827007058867883^1024*100000^4123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16781 100000 37827007058867883 50000000000000000000 4123 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16781/100000 : ℝ)) (X := (37827007058867883/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002627924563901701/25000000000000000000 : ℝ) ≤ (5000130530606473/5000000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (25002627924563901701/25000000000000000000 : ℝ)^1024 ≤ (5000130530606473/5000000000000000 : ℝ)^4123 := by
      have hnat : (25002627924563901701 : ℕ)^1024*5000000000000000^4123 ≤ 5000130530606473^4123*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002627924563901701 25000000000000000000 5000130530606473 5000000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000130530606473/5000000000000000 : ℝ)) (X := (25002627924563901701/25000000000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3127528433226423099/3125000000000000000 : ℝ) ≤ (10002008889614017/10000000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (3127528433226423099/3125000000000000000 : ℝ)^1024 ≤ (10002008889614017/10000000000000000 : ℝ)^4123 := by
      have hnat : (3127528433226423099 : ℕ)^1024*10000000000000000^4123 ≤ 10002008889614017^4123*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127528433226423099 3125000000000000000 10002008889614017 10000000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002008889614017/10000000000000000 : ℝ)) (X := (3127528433226423099/3125000000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25037827007058867883/25000000000000000000 : ℝ) ≤ (625234794875943/625000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (25037827007058867883/25000000000000000000 : ℝ)^1024 ≤ (625234794875943/625000000000000 : ℝ)^4123 := by
      have hnat : (25037827007058867883 : ℕ)^1024*625000000000000^4123 ≤ 625234794875943^4123*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25037827007058867883 25000000000000000000 625234794875943 625000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625234794875943/625000000000000 : ℝ)) (X := (25037827007058867883/25000000000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2627924563901701/50000000000000000000 : ℝ) ≤ ((40625936993614945181/40640000000000000000 : ℝ)+2*(1747828401071/812800000000000 : ℝ)*(8653/100000 : ℝ))^(4123/1024 : ℝ) := by
    rw [show (40625936993614945181/40640000000000000000 : ℝ)+2*(1747828401071/812800000000000 : ℝ)*(8653/100000 : ℝ)=(5000130530606473/5000000000000000 : ℝ) by norm_num, show 1+2*(2627924563901701/50000000000000000000 : ℝ)=(25002627924563901701/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37827007058867883/50000000000000000000 : ℝ)+(2627924563901701/50000000000000000000 : ℝ) ≤ ((40625936993614945181/40640000000000000000 : ℝ)+(1747828401071/812800000000000 : ℝ)*((16781/100000 : ℝ)+(8653/100000 : ℝ)))^(4123/1024 : ℝ) := by
    rw [show (40625936993614945181/40640000000000000000 : ℝ)+(1747828401071/812800000000000 : ℝ)*((16781/100000 : ℝ)+(8653/100000 : ℝ))=(10002008889614017/10000000000000000 : ℝ) by norm_num, show 1+(37827007058867883/50000000000000000000 : ℝ)+(2627924563901701/50000000000000000000 : ℝ)=(3127528433226423099/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37827007058867883/50000000000000000000 : ℝ) ≤ ((40625936993614945181/40640000000000000000 : ℝ)+2*(1747828401071/812800000000000 : ℝ)*(16781/100000 : ℝ))^(4123/1024 : ℝ) := by
    rw [show (40625936993614945181/40640000000000000000 : ℝ)+2*(1747828401071/812800000000000 : ℝ)*(16781/100000 : ℝ)=(625234794875943/625000000000000 : ℝ) by norm_num, show 1+2*(37827007058867883/50000000000000000000 : ℝ)=(25037827007058867883/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (40625936993614945181/40640000000000000000 : ℝ)*(X 1 0+X 2 0)+(1747828401071/812800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (8653/100000 : ℝ)) (hi := (16781/100000 : ℝ)) (c := (40625936993614945181/40640000000000000000 : ℝ)) (alpha := (1747828401071/812800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (40625936993614945181/40640000000000000000 : ℝ)*(X 0 1+X 2 1)+(1747828401071/812800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (8653/100000 : ℝ)) (hi := (16781/100000 : ℝ)) (c := (40625936993614945181/40640000000000000000 : ℝ)) (alpha := (1747828401071/812800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (40625936993614945181/40640000000000000000 : ℝ)*(X 0 2+X 1 2)+(1747828401071/812800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (8653/100000 : ℝ)) (hi := (16781/100000 : ℝ)) (c := (40625936993614945181/40640000000000000000 : ℝ)) (alpha := (1747828401071/812800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2204781509/10000000000 : ℝ)*X 0 0+(1087790581/2000000000 : ℝ)*X 0 1+(5223052879/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5356004259/10000000000 : ℝ)*X 1 0+(-1157686659/5000000000 : ℝ)*X 1 1+(5223052763/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5356004171/10000000000 : ℝ)*X 2 0+(522305261/1000000000 : ℝ)*X 2 1+(-2315373633/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2187160531/5000000000 : ℝ)*X 0 0+(4168422611/10000000000 : ℝ)*X 0 1+(573818739/1250000000 : ℝ)*X 0 2+(2187160531/5000000000 : ℝ)*X 1 0+(4168422611/10000000000 : ℝ)*X 1 1+(573818739/1250000000 : ℝ)*X 1 2+(2187160531/5000000000 : ℝ)*X 2 0+(4168422611/10000000000 : ℝ)*X 2 1+(573818739/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-34450071/156250000 : ℝ)*X 0 0+(5223945001/10000000000 : ℝ)*X 0 1+(2719027749/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325417627/2500000000 : ℝ)*X 1 0+(-2100371191/10000000000 : ℝ)*X 1 1+(5438054877/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301670199/10000000000 : ℝ)*X 2 0+(5438055339/10000000000 : ℝ)*X 2 1+(-2100370979/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4374366221/10000000000 : ℝ)*X 0 0+(2294402117/5000000000 : ℝ)*X 0 1+(2085089349/5000000000 : ℝ)*X 0 2+(4374366221/10000000000 : ℝ)*X 1 0+(2294402117/5000000000 : ℝ)*X 1 1+(2085089349/5000000000 : ℝ)*X 1 2+(4374366221/10000000000 : ℝ)*X 2 0+(2294402117/5000000000 : ℝ)*X 2 1+(2085089349/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7701354655465416886473297753/2032000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (758534247/100000000000000 : ℝ)*(base19) + (364801093/50000000000000 : ℝ)*(base23) + (34275851/100000000000000 : ℝ)*(upper2) + (12896401/6250000000000 : ℝ)*(upper3) + (3500379291099471/100000000000000 : ℝ)*(major0) + (3500379291099471/100000000000000 : ℝ)*(major1) + (3500379291099471/100000000000000 : ℝ)*(major2) + (4631785415769603/100000000000000 : ℝ)*(sp0) + (463178941422977/10000000000000 : ℝ)*(sp1) + (463178778450757/10000000000000 : ℝ)*(sp2) + (592239965062067/25000000000000 : ℝ)*(sp3) + (951398883/20000000000000 : ℝ)*(sp4) + (1658654261/100000000000000 : ℝ)*(sp6) + (1684570419/20000000000000 : ℝ)*(sp7) + (2368968283100363/100000000000000 : ℝ)*(f.failure) + (4631790172764017/100000000000000 : ℝ)*(f.sum) + (59812571982081/40640000000000000000000000000 : ℝ)*base65 + (18717951459356850749/4064000000000000000000000000000000 : ℝ)*base68 + (17984526764156850749/4064000000000000000000000000000000 : ℝ)*base70 + (2126752467068850749/4064000000000000000000000000000000 : ℝ)*base72 + (57314760702079/40640000000000000000000000000 : ℝ)*base74 + (13229131700451149251/4064000000000000000000000000000000 : ℝ)*base75 + (29617891709724850749/4064000000000000000000000000000000 : ℝ)*base78 + (15550952117507149251/4064000000000000000000000000000000 : ℝ)*base79 + (58267419959361/40640000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (4488419/2500000000000000000000 : ℝ)*base89 + (4488419/2500000000000000000000 : ℝ)*base91 + (4488419/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (90081078805651717490915157/8000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (552504497/25000000000000 : ℝ)*(base19) + (998708819/50000000000000 : ℝ)*(base23) + (61696349/100000000000000 : ℝ)*(upper3) + (6126627/12500000000000 : ℝ)*(lower4) + (215111283/50000000000000 : ℝ)*(upper5) + (1764814576167827/50000000000000 : ℝ)*(major0) + (1764814576167827/50000000000000 : ℝ)*(major1) + (1764814576167827/50000000000000 : ℝ)*(major2) + (30532911337/100000000000000 : ℝ)*(sp1) + (13664402149/50000000000000 : ℝ)*(sp2) + (291905879938299/6250000000000 : ℝ)*(sp4) + (4670461336083459/100000000000000 : ℝ)*(sp5) + (72976011762357/1562500000000 : ℝ)*(sp6) + (2388763850320691/100000000000000 : ℝ)*(sp7) + (2388763850320691/100000000000000 : ℝ)*(f.failure) + (291905879938299/6250000000000 : ℝ)*(f.sum) + (538176708771/160000000000000000000000000 : ℝ)*base65 + (65327426720478281/16000000000000000000000000000000 : ℝ)*base67 + (85183425631521719/16000000000000000000000000000000 : ℝ)*base70 + (3832440287521719/16000000000000000000000000000000 : ℝ)*base72 + (60835645731/160000000000000000000000000 : ℝ)*base73 + (154778698496478281/16000000000000000000000000000000 : ℝ)*base75 + (28104291632478281/16000000000000000000000000000000 : ℝ)*base77 + (209760027232478281/16000000000000000000000000000000 : ℝ)*base79 + (604875655549/160000000000000000000000000 : ℝ)*base82 + (2360117/2500000000000000000000 : ℝ)*base90 + (2360117/2500000000000000000000 : ℝ)*base92 + (2360117/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1054_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16781/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8653/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2589/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3731/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1054_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1054_s4_0 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2208578617/10000000000 : ℝ)*x 0 + (540649269/1000000000 : ℝ)*x 1 + (65662913/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2208578617/10000000000 : ℝ)^8247 ≤ (13409839551147/100000000000000 : ℝ)^6199 := by
    have hnat : (2208578617 : ℕ)^8247*100000000000000^6199 ≤ 13409839551147^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208578617 10000000000 13409839551147 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540649269/1000000000 : ℝ)^8247 ≤ (44124255078631/100000000000000 : ℝ)^6199 := by
    have hnat : (540649269 : ℕ)^8247*100000000000000^6199 ≤ 44124255078631^6199*1000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540649269 1000000000 44124255078631 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65662913/125000000 : ℝ)^8247 ≤ (21232952675783/50000000000000 : ℝ)^6199 := by
    have hnat : (65662913 : ℕ)^8247*50000000000000^6199 ≤ 21232952675783^6199*125000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65662913 125000000 21232952675783 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2208578617/10000000000 : ℝ), (540649269/1000000000 : ℝ), (65662913/125000000 : ℝ)] ![(13409839551147/100000000000000 : ℝ), (44124255078631/100000000000000 : ℝ), (21232952675783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2208578617/10000000000 : ℝ)|^8247 ≤ (13409839551147/100000000000000 : ℝ)^6199
        have hw : |(-2208578617/10000000000 : ℝ)|=(2208578617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540649269/1000000000 : ℝ)|^8247 ≤ (44124255078631/100000000000000 : ℝ)^6199
        have hw : |(540649269/1000000000 : ℝ)|=(540649269/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65662913/125000000 : ℝ)|^8247 ≤ (21232952675783/50000000000000 : ℝ)^6199
        have hw : |(65662913/125000000 : ℝ)|=(65662913/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s4_1 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2673986783/5000000000 : ℝ)*x 0 + (-1143321813/5000000000 : ℝ)*x 1 + (5253033663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673986783/5000000000 : ℝ)^8247 ≤ (43490013291769/100000000000000 : ℝ)^6199 := by
    have hnat : (2673986783 : ℕ)^8247*100000000000000^6199 ≤ 43490013291769^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673986783 5000000000 43490013291769 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1143321813/5000000000 : ℝ)^8247 ≤ (14044074636127/100000000000000 : ℝ)^6199 := by
    have hnat : (1143321813 : ℕ)^8247*100000000000000^6199 ≤ 14044074636127^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143321813 5000000000 14044074636127 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253033663/10000000000 : ℝ)^8247 ≤ (42465912051841/100000000000000 : ℝ)^6199 := by
    have hnat : (5253033663 : ℕ)^8247*100000000000000^6199 ≤ 42465912051841^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253033663 10000000000 42465912051841 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673986783/5000000000 : ℝ), (-1143321813/5000000000 : ℝ), (5253033663/10000000000 : ℝ)] ![(43490013291769/100000000000000 : ℝ), (14044074636127/100000000000000 : ℝ), (42465912051841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673986783/5000000000 : ℝ)|^8247 ≤ (43490013291769/100000000000000 : ℝ)^6199
        have hw : |(2673986783/5000000000 : ℝ)|=(2673986783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1143321813/5000000000 : ℝ)|^8247 ≤ (14044074636127/100000000000000 : ℝ)^6199
        have hw : |(-1143321813/5000000000 : ℝ)|=(1143321813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253033663/10000000000 : ℝ)|^8247 ≤ (42465912051841/100000000000000 : ℝ)^6199
        have hw : |(5253033663/10000000000 : ℝ)|=(5253033663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s4_2 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336993271/2500000000 : ℝ)*x 0 + (2626517097/5000000000 : ℝ)*x 1 + (-1143321783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336993271/2500000000 : ℝ)^8247 ≤ (43490008077161/100000000000000 : ℝ)^6199 := by
    have hnat : (1336993271 : ℕ)^8247*100000000000000^6199 ≤ 43490008077161^6199*2500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336993271 2500000000 43490008077161 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2626517097/5000000000 : ℝ)^8247 ≤ (4246591776267/10000000000000 : ℝ)^6199 := by
    have hnat : (2626517097 : ℕ)^8247*10000000000000^6199 ≤ 4246591776267^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626517097 5000000000 4246591776267 10000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1143321783/5000000000 : ℝ)^8247 ≤ (7022037072937/50000000000000 : ℝ)^6199 := by
    have hnat : (1143321783 : ℕ)^8247*50000000000000^6199 ≤ 7022037072937^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143321783 5000000000 7022037072937 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336993271/2500000000 : ℝ), (2626517097/5000000000 : ℝ), (-1143321783/5000000000 : ℝ)] ![(43490008077161/100000000000000 : ℝ), (4246591776267/10000000000000 : ℝ), (7022037072937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336993271/2500000000 : ℝ)|^8247 ≤ (43490008077161/100000000000000 : ℝ)^6199
        have hw : |(1336993271/2500000000 : ℝ)|=(1336993271/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2626517097/5000000000 : ℝ)|^8247 ≤ (4246591776267/10000000000000 : ℝ)^6199
        have hw : |(2626517097/5000000000 : ℝ)|=(2626517097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1143321783/5000000000 : ℝ)|^8247 ≤ (7022037072937/50000000000000 : ℝ)^6199
        have hw : |(-1143321783/5000000000 : ℝ)|=(1143321783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s4_3 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (280101/640000 : ℝ)*x 0 + (4229168967/10000000000 : ℝ)*x 1 + (2264605199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (280101/640000 : ℝ)^8247 ≤ (33309970328807/100000000000000 : ℝ)^6199 := by
    have hnat : (280101 : ℕ)^8247*100000000000000^6199 ≤ 33309970328807^6199*640000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280101 640000 33309970328807 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4229168967/10000000000 : ℝ)^8247 ≤ (3182575538697/10000000000000 : ℝ)^6199 := by
    have hnat : (4229168967 : ℕ)^8247*10000000000000^6199 ≤ 3182575538697^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229168967 10000000000 3182575538697 10000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2264605199/5000000000 : ℝ)^8247 ≤ (17432137135711/50000000000000 : ℝ)^6199 := by
    have hnat : (2264605199 : ℕ)^8247*50000000000000^6199 ≤ 17432137135711^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264605199 5000000000 17432137135711 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(280101/640000 : ℝ), (4229168967/10000000000 : ℝ), (2264605199/5000000000 : ℝ)] ![(33309970328807/100000000000000 : ℝ), (3182575538697/10000000000000 : ℝ), (17432137135711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(280101/640000 : ℝ)|^8247 ≤ (33309970328807/100000000000000 : ℝ)^6199
        have hw : |(280101/640000 : ℝ)|=(280101/640000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4229168967/10000000000 : ℝ)|^8247 ≤ (3182575538697/10000000000000 : ℝ)^6199
        have hw : |(4229168967/10000000000 : ℝ)|=(4229168967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2264605199/5000000000 : ℝ)|^8247 ≤ (17432137135711/50000000000000 : ℝ)^6199
        have hw : |(2264605199/5000000000 : ℝ)|=(2264605199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s4_4 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2208586729/10000000000 : ℝ)*x 0 + (1313371411/2500000000 : ℝ)*x 1 + (1351509581/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2208586729/10000000000 : ℝ)^8247 ≤ (1340990507709/10000000000000 : ℝ)^6199 := by
    have hnat : (2208586729 : ℕ)^8247*10000000000000^6199 ≤ 1340990507709^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208586729 10000000000 1340990507709 10000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313371411/2500000000 : ℝ)^8247 ≤ (265442331949/625000000000 : ℝ)^6199 := by
    have hnat : (1313371411 : ℕ)^8247*625000000000^6199 ≤ 265442331949^6199*2500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313371411 2500000000 265442331949 625000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351509581/2500000000 : ℝ)^8247 ≤ (44119321796863/100000000000000 : ℝ)^6199 := by
    have hnat : (1351509581 : ℕ)^8247*100000000000000^6199 ≤ 44119321796863^6199*2500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351509581 2500000000 44119321796863 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2208586729/10000000000 : ℝ), (1313371411/2500000000 : ℝ), (1351509581/2500000000 : ℝ)] ![(1340990507709/10000000000000 : ℝ), (265442331949/625000000000 : ℝ), (44119321796863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2208586729/10000000000 : ℝ)|^8247 ≤ (1340990507709/10000000000000 : ℝ)^6199
        have hw : |(-2208586729/10000000000 : ℝ)|=(2208586729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313371411/2500000000 : ℝ)|^8247 ≤ (265442331949/625000000000 : ℝ)^6199
        have hw : |(1313371411/2500000000 : ℝ)|=(1313371411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351509581/2500000000 : ℝ)|^8247 ≤ (44119321796863/100000000000000 : ℝ)^6199
        have hw : |(1351509581/2500000000 : ℝ)|=(1351509581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s4_5 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5309359839/10000000000 : ℝ)*x 0 + (-133352393/625000000 : ℝ)*x 1 + (5406038229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5309359839/10000000000 : ℝ)^8247 ≤ (10768190608429/25000000000000 : ℝ)^6199 := by
    have hnat : (5309359839 : ℕ)^8247*25000000000000^6199 ≤ 10768190608429^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5309359839 10000000000 10768190608429 25000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (133352393/625000000 : ℝ)^8247 ≤ (12807916791389/100000000000000 : ℝ)^6199 := by
    have hnat : (133352393 : ℕ)^8247*100000000000000^6199 ≤ 12807916791389^6199*625000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133352393 625000000 12807916791389 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406038229/10000000000 : ℝ)^8247 ≤ (22059660382707/50000000000000 : ℝ)^6199 := by
    have hnat : (5406038229 : ℕ)^8247*50000000000000^6199 ≤ 22059660382707^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406038229 10000000000 22059660382707 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5309359839/10000000000 : ℝ), (-133352393/625000000 : ℝ), (5406038229/10000000000 : ℝ)] ![(10768190608429/25000000000000 : ℝ), (12807916791389/100000000000000 : ℝ), (22059660382707/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5309359839/10000000000 : ℝ)|^8247 ≤ (10768190608429/25000000000000 : ℝ)^6199
        have hw : |(5309359839/10000000000 : ℝ)|=(5309359839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-133352393/625000000 : ℝ)|^8247 ≤ (12807916791389/100000000000000 : ℝ)^6199
        have hw : |(-133352393/625000000 : ℝ)|=(133352393/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406038229/10000000000 : ℝ)|^8247 ≤ (22059660382707/50000000000000 : ℝ)^6199
        have hw : |(5406038229/10000000000 : ℝ)|=(5406038229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s4_6 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2654679729/5000000000 : ℝ)*x 0 + (168938701/312500000 : ℝ)*x 1 + (-2133638527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2654679729/5000000000 : ℝ)^8247 ≤ (43072758321651/100000000000000 : ℝ)^6199 := by
    have hnat : (2654679729 : ℕ)^8247*100000000000000^6199 ≤ 43072758321651^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2654679729 5000000000 43072758321651 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168938701/312500000 : ℝ)^8247 ≤ (44119322969457/100000000000000 : ℝ)^6199 := by
    have hnat : (168938701 : ℕ)^8247*100000000000000^6199 ≤ 44119322969457^6199*312500000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168938701 312500000 44119322969457 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2133638527/10000000000 : ℝ)^8247 ≤ (2561583740011/20000000000000 : ℝ)^6199 := by
    have hnat : (2133638527 : ℕ)^8247*20000000000000^6199 ≤ 2561583740011^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133638527 10000000000 2561583740011 20000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2654679729/5000000000 : ℝ), (168938701/312500000 : ℝ), (-2133638527/10000000000 : ℝ)] ![(43072758321651/100000000000000 : ℝ), (44119322969457/100000000000000 : ℝ), (2561583740011/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2654679729/5000000000 : ℝ)|^8247 ≤ (43072758321651/100000000000000 : ℝ)^6199
        have hw : |(2654679729/5000000000 : ℝ)|=(2654679729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168938701/312500000 : ℝ)|^8247 ≤ (44119322969457/100000000000000 : ℝ)^6199
        have hw : |(168938701/312500000 : ℝ)|=(168938701/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2133638527/10000000000 : ℝ)|^8247 ≤ (2561583740011/20000000000000 : ℝ)^6199
        have hw : |(-2133638527/10000000000 : ℝ)|=(2133638527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s4_7 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4376594933/10000000000 : ℝ)*x 0 + (2264163111/5000000000 : ℝ)*x 1 + (4230056333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4376594933/10000000000 : ℝ)^8247 ≤ (8327535129329/25000000000000 : ℝ)^6199 := by
    have hnat : (4376594933 : ℕ)^8247*25000000000000^6199 ≤ 8327535129329^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4376594933 10000000000 8327535129329 25000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2264163111/5000000000 : ℝ)^8247 ≤ (34855219922877/100000000000000 : ℝ)^6199 := by
    have hnat : (2264163111 : ℕ)^8247*100000000000000^6199 ≤ 34855219922877^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264163111 5000000000 34855219922877 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4230056333/10000000000 : ℝ)^8247 ≤ (50935423259/160000000000 : ℝ)^6199 := by
    have hnat : (4230056333 : ℕ)^8247*160000000000^6199 ≤ 50935423259^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230056333 10000000000 50935423259 160000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4376594933/10000000000 : ℝ), (2264163111/5000000000 : ℝ), (4230056333/10000000000 : ℝ)] ![(8327535129329/25000000000000 : ℝ), (34855219922877/100000000000000 : ℝ), (50935423259/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4376594933/10000000000 : ℝ)|^8247 ≤ (8327535129329/25000000000000 : ℝ)^6199
        have hw : |(4376594933/10000000000 : ℝ)|=(4376594933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2264163111/5000000000 : ℝ)|^8247 ≤ (34855219922877/100000000000000 : ℝ)^6199
        have hw : |(2264163111/5000000000 : ℝ)|=(2264163111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4230056333/10000000000 : ℝ)|^8247 ≤ (50935423259/160000000000 : ℝ)^6199
        have hw : |(4230056333/10000000000 : ℝ)|=(4230056333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1054_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3731/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2589/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (2749/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2849/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3731/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2589/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3731/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2589/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3731/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2589/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3731/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2589/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3731/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2589/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3731/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2589/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2589/25000 : ℝ) ^ (4123/1024 : ℝ) ≤ (2708579328314859/25000000000000000000 : ℝ) := by
    have hpowers : (2589/25000 : ℝ)^4123 ≤ (2708579328314859/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2589 : ℕ)^4123*25000000000000000000^1024 ≤ 2708579328314859^1024*25000^4123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2589 25000 2708579328314859 25000000000000000000 4123 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2589/25000 : ℝ)) (X := (2708579328314859/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3731/25000 : ℝ) ^ (4123/1024 : ℝ) ≤ (47180076280094407/100000000000000000000 : ℝ) := by
    have hpowers : (3731/25000 : ℝ)^4123 ≤ (47180076280094407/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3731 : ℕ)^4123*100000000000000000000^1024 ≤ 47180076280094407^1024*25000^4123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3731 25000 47180076280094407 100000000000000000000 4123 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3731/25000 : ℝ)) (X := (47180076280094407/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502708579328314859/12500000000000000000 : ℝ) ≤ (400021524981961/400000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (12502708579328314859/12500000000000000000 : ℝ)^1024 ≤ (400021524981961/400000000000000 : ℝ)^4123 := by
      have hnat : (12502708579328314859 : ℕ)^1024*400000000000000^4123 ≤ 400021524981961^4123*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502708579328314859 12500000000000000000 400021524981961 400000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400021524981961/400000000000000 : ℝ)) (X := (12502708579328314859/12500000000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100058014393593353843/100000000000000000000 : ℝ) ≤ (2000288109585453/2000000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (100058014393593353843/100000000000000000000 : ℝ)^1024 ≤ (2000288109585453/2000000000000000 : ℝ)^4123 := by
      have hnat : (100058014393593353843 : ℕ)^1024*2000000000000000^4123 ≤ 2000288109585453^4123*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100058014393593353843 100000000000000000000 2000288109585453 2000000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000288109585453/2000000000000000 : ℝ)) (X := (100058014393593353843/100000000000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50047180076280094407/50000000000000000000 : ℝ) ≤ (2000468594261101/2000000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (50047180076280094407/50000000000000000000 : ℝ)^1024 ≤ (2000468594261101/2000000000000000 : ℝ)^4123 := by
      have hnat : (50047180076280094407 : ℕ)^1024*2000000000000000^4123 ≤ 2000468594261101^4123*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50047180076280094407 50000000000000000000 2000468594261101 2000000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000468594261101/2000000000000000 : ℝ)) (X := (50047180076280094407/50000000000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2708579328314859/25000000000000000000 : ℝ) ≤ ((1141594178998245983/1142000000000000000 : ℝ)+2*(2820073057/1427500000000 : ℝ)*(2589/25000 : ℝ))^(4123/1024 : ℝ) := by
    rw [show (1141594178998245983/1142000000000000000 : ℝ)+2*(2820073057/1427500000000 : ℝ)*(2589/25000 : ℝ)=(400021524981961/400000000000000 : ℝ) by norm_num, show 1+2*(2708579328314859/25000000000000000000 : ℝ)=(12502708579328314859/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(47180076280094407/100000000000000000000 : ℝ)+(2708579328314859/25000000000000000000 : ℝ) ≤ ((1141594178998245983/1142000000000000000 : ℝ)+(2820073057/1427500000000 : ℝ)*((3731/25000 : ℝ)+(2589/25000 : ℝ)))^(4123/1024 : ℝ) := by
    rw [show (1141594178998245983/1142000000000000000 : ℝ)+(2820073057/1427500000000 : ℝ)*((3731/25000 : ℝ)+(2589/25000 : ℝ))=(2000288109585453/2000000000000000 : ℝ) by norm_num, show 1+(47180076280094407/100000000000000000000 : ℝ)+(2708579328314859/25000000000000000000 : ℝ)=(100058014393593353843/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(47180076280094407/100000000000000000000 : ℝ) ≤ ((1141594178998245983/1142000000000000000 : ℝ)+2*(2820073057/1427500000000 : ℝ)*(3731/25000 : ℝ))^(4123/1024 : ℝ) := by
    rw [show (1141594178998245983/1142000000000000000 : ℝ)+2*(2820073057/1427500000000 : ℝ)*(3731/25000 : ℝ)=(2000468594261101/2000000000000000 : ℝ) by norm_num, show 1+2*(47180076280094407/100000000000000000000 : ℝ)=(50047180076280094407/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1141594178998245983/1142000000000000000 : ℝ)*(X 1 0+X 2 0)+(2820073057/1427500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (2589/25000 : ℝ)) (hi := (3731/25000 : ℝ)) (c := (1141594178998245983/1142000000000000000 : ℝ)) (alpha := (2820073057/1427500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1141594178998245983/1142000000000000000 : ℝ)*(X 0 1+X 2 1)+(2820073057/1427500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (2589/25000 : ℝ)) (hi := (3731/25000 : ℝ)) (c := (1141594178998245983/1142000000000000000 : ℝ)) (alpha := (2820073057/1427500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1141594178998245983/1142000000000000000 : ℝ)*(X 0 2+X 1 2)+(2820073057/1427500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (2589/25000 : ℝ)) (hi := (3731/25000 : ℝ)) (c := (1141594178998245983/1142000000000000000 : ℝ)) (alpha := (2820073057/1427500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2208578617/10000000000 : ℝ)*X 0 0+(540649269/1000000000 : ℝ)*X 0 1+(65662913/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673986783/5000000000 : ℝ)*X 1 0+(-1143321813/5000000000 : ℝ)*X 1 1+(5253033663/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336993271/2500000000 : ℝ)*X 2 0+(2626517097/5000000000 : ℝ)*X 2 1+(-1143321783/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((280101/640000 : ℝ)*X 0 0+(4229168967/10000000000 : ℝ)*X 0 1+(2264605199/5000000000 : ℝ)*X 0 2+(280101/640000 : ℝ)*X 1 0+(4229168967/10000000000 : ℝ)*X 1 1+(2264605199/5000000000 : ℝ)*X 1 2+(280101/640000 : ℝ)*X 2 0+(4229168967/10000000000 : ℝ)*X 2 1+(2264605199/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2208586729/10000000000 : ℝ)*X 0 0+(1313371411/2500000000 : ℝ)*X 0 1+(1351509581/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5309359839/10000000000 : ℝ)*X 1 0+(-133352393/625000000 : ℝ)*X 1 1+(5406038229/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2654679729/5000000000 : ℝ)*X 2 0+(168938701/312500000 : ℝ)*X 2 1+(-2133638527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4376594933/10000000000 : ℝ)*X 0 0+(2264163111/5000000000 : ℝ)*X 0 1+(4230056333/10000000000 : ℝ)*X 0 2+(4376594933/10000000000 : ℝ)*X 1 0+(2264163111/5000000000 : ℝ)*X 1 1+(4230056333/10000000000 : ℝ)*X 1 2+(4376594933/10000000000 : ℝ)*X 2 0+(2264163111/5000000000 : ℝ)*X 2 1+(4230056333/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (570066716185805805134709411/57100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (348616743/50000000000000 : ℝ)*(base19) + (54254951/50000000000000 : ℝ)*(base23) + (88716371/50000000000000 : ℝ)*(upper3) + (23591/3125000000000 : ℝ)*(upper4) + (28704299/20000000000000 : ℝ)*(upper5) + (4924672246740639/100000000000000 : ℝ)*(major0) + (4924672246740639/100000000000000 : ℝ)*(major1) + (4924672246740639/100000000000000 : ℝ)*(major2) + (81455172687947/1250000000000 : ℝ)*(sp0) + (1629112421561389/25000000000000 : ℝ)*(sp1) + (6516450274969141/100000000000000 : ℝ)*(sp2) + (1666442206943263/50000000000000 : ℝ)*(sp3) + (36568443283/100000000000000 : ℝ)*(sp4) + (2340831797/25000000000000 : ℝ)*(sp7) + (3332893777213713/100000000000000 : ℝ)*(f.failure) + (3258225191739521/50000000000000 : ℝ)*(f.sum) + (2182615712067/571000000000000000000000000 : ℝ)*base65 + (555456835837003137/114200000000000000000000000000000 : ℝ)*base67 + (202120955961796863/114200000000000000000000000000000 : ℝ)*base70 + (1129007056593003137/114200000000000000000000000000000 : ℝ)*base71 + (167715566239/285500000000000000000000000 : ℝ)*base74 + (290313451772996863/114200000000000000000000000000000 : ℝ)*base76 + (895259677908596863/114200000000000000000000000000000 : ℝ)*base78 + (674532402931396863/114200000000000000000000000000000 : ℝ)*base80 + (704240248991/285500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (34373031/2500000000000000000000 : ℝ)*base90 + (34373031/2500000000000000000000 : ℝ)*base92 + (34373031/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5337430709563218395977359/2855000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (979420651/100000000000000 : ℝ)*(base19) + (121508987/12500000000000 : ℝ)*(base23) + (6983949/100000000000000 : ℝ)*(upper3) + (256739031/100000000000000 : ℝ)*(lower4) + (872721/2000000000000 : ℝ)*(upper5) + (247694174391091/5000000000000 : ℝ)*(major0) + (247694174391091/5000000000000 : ℝ)*(major1) + (247694174391091/5000000000000 : ℝ)*(major2) + (24880608299/100000000000000 : ℝ)*(sp1) + (2206007967/10000000000000 : ℝ)*(sp2) + (6555103706038173/100000000000000 : ℝ)*(sp4) + (6555077846009223/100000000000000 : ℝ)*(sp5) + (6555080673886607/100000000000000 : ℝ)*(sp6) + (3352663207288699/100000000000000 : ℝ)*(sp7) + (3352663207288699/100000000000000 : ℝ)*(f.failure) + (6555103706038173/100000000000000 : ℝ)*(f.sum) + (50918967463/57100000000000000000000000 : ℝ)*base66 + (18174509787562547/5710000000000000000000000000000 : ℝ)*base68 + (53593464085152547/5710000000000000000000000000000 : ℝ)*base70 + (21260303857757453/5710000000000000000000000000000 : ℝ)*base71 + (38153576873/28550000000000000000000000 : ℝ)*base74 + (120650637754072547/5710000000000000000000000000000 : ℝ)*base76 + (7107715094707453/5710000000000000000000000000000 : ℝ)*base77 + (59028576479882547/5710000000000000000000000000000 : ℝ)*base80 + (234756472399/285500000000000000000000000 : ℝ)*base82 + (6943187/2500000000000000000000 : ℝ)*base89 + (6943187/2500000000000000000000 : ℝ)*base91 + (6943187/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1054_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3731/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2589/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2749/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2849/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1054_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1054_s5_0 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2209447271/10000000000 : ℝ)*x 0 + (269867233/500000000 : ℝ)*x 1 + (2630805577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2209447271/10000000000 : ℝ)^8247 ≤ (13416856690693/100000000000000 : ℝ)^6199 := by
    have hnat : (2209447271 : ℕ)^8247*100000000000000^6199 ≤ 13416856690693^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209447271 10000000000 13416856690693 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269867233/500000000 : ℝ)^8247 ≤ (11006239169457/25000000000000 : ℝ)^6199 := by
    have hnat : (269867233 : ℕ)^8247*25000000000000^6199 ≤ 11006239169457^6199*500000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269867233 500000000 11006239169457 25000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630805577/5000000000 : ℝ)^8247 ≤ (5319773326531/12500000000000 : ℝ)^6199 := by
    have hnat : (2630805577 : ℕ)^8247*12500000000000^6199 ≤ 5319773326531^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630805577 5000000000 5319773326531 12500000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2209447271/10000000000 : ℝ), (269867233/500000000 : ℝ), (2630805577/5000000000 : ℝ)] ![(13416856690693/100000000000000 : ℝ), (11006239169457/25000000000000 : ℝ), (5319773326531/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2209447271/10000000000 : ℝ)|^8247 ≤ (13416856690693/100000000000000 : ℝ)^6199
        have hw : |(-2209447271/10000000000 : ℝ)|=(2209447271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269867233/500000000 : ℝ)|^8247 ≤ (11006239169457/25000000000000 : ℝ)^6199
        have hw : |(269867233/500000000 : ℝ)|=(269867233/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630805577/5000000000 : ℝ)|^8247 ≤ (5319773326531/12500000000000 : ℝ)^6199
        have hw : |(2630805577/5000000000 : ℝ)|=(2630805577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s5_1 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345697503/10000000000 : ℝ)*x 0 + (-2278359117/10000000000 : ℝ)*x 1 + (328850691/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345697503/10000000000 : ℝ)^8247 ≤ (21732695502379/50000000000000 : ℝ)^6199 := by
    have hnat : (5345697503 : ℕ)^8247*50000000000000^6199 ≤ 21732695502379^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345697503 10000000000 21732695502379 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2278359117/10000000000 : ℝ)^8247 ≤ (13976423425469/100000000000000 : ℝ)^6199 := by
    have hnat : (2278359117 : ℕ)^8247*100000000000000^6199 ≤ 13976423425469^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2278359117 10000000000 13976423425469 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (328850691/625000000 : ℝ)^8247 ≤ (5319773194713/12500000000000 : ℝ)^6199 := by
    have hnat : (328850691 : ℕ)^8247*12500000000000^6199 ≤ 5319773194713^6199*625000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328850691 625000000 5319773194713 12500000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345697503/10000000000 : ℝ), (-2278359117/10000000000 : ℝ), (328850691/625000000 : ℝ)] ![(21732695502379/50000000000000 : ℝ), (13976423425469/100000000000000 : ℝ), (5319773194713/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345697503/10000000000 : ℝ)|^8247 ≤ (21732695502379/50000000000000 : ℝ)^6199
        have hw : |(5345697503/10000000000 : ℝ)|=(5345697503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2278359117/10000000000 : ℝ)|^8247 ≤ (13976423425469/100000000000000 : ℝ)^6199
        have hw : |(-2278359117/10000000000 : ℝ)|=(2278359117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(328850691/625000000 : ℝ)|^8247 ≤ (5319773194713/12500000000000 : ℝ)^6199
        have hw : |(328850691/625000000 : ℝ)|=(328850691/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s5_2 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345697373/10000000000 : ℝ)*x 0 + (5261611159/10000000000 : ℝ)*x 1 + (-2278359153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345697373/10000000000 : ℝ)^8247 ≤ (21732694799263/50000000000000 : ℝ)^6199 := by
    have hnat : (5345697373 : ℕ)^8247*50000000000000^6199 ≤ 21732694799263^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345697373 10000000000 21732694799263 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261611159/10000000000 : ℝ)^8247 ≤ (42558186666051/100000000000000 : ℝ)^6199 := by
    have hnat : (5261611159 : ℕ)^8247*100000000000000^6199 ≤ 42558186666051^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261611159 10000000000 42558186666051 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2278359153/10000000000 : ℝ)^8247 ≤ (3494105929817/25000000000000 : ℝ)^6199 := by
    have hnat : (2278359153 : ℕ)^8247*25000000000000^6199 ≤ 3494105929817^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2278359153 10000000000 3494105929817 25000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345697373/10000000000 : ℝ), (5261611159/10000000000 : ℝ), (-2278359153/10000000000 : ℝ)] ![(21732694799263/50000000000000 : ℝ), (42558186666051/100000000000000 : ℝ), (3494105929817/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345697373/10000000000 : ℝ)|^8247 ≤ (21732694799263/50000000000000 : ℝ)^6199
        have hw : |(5345697373/10000000000 : ℝ)|=(5345697373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261611159/10000000000 : ℝ)|^8247 ≤ (42558186666051/100000000000000 : ℝ)^6199
        have hw : |(5261611159/10000000000 : ℝ)|=(5261611159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2278359153/10000000000 : ℝ)|^8247 ≤ (3494105929817/25000000000000 : ℝ)^6199
        have hw : |(-2278359153/10000000000 : ℝ)|=(2278359153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s5_3 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2188540089/5000000000 : ℝ)*x 0 + (849286151/2000000000 : ℝ)*x 1 + (902363257/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2188540089/5000000000 : ℝ)^8247 ≤ (8328763483207/25000000000000 : ℝ)^6199 := by
    have hnat : (2188540089 : ℕ)^8247*25000000000000^6199 ≤ 8328763483207^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188540089 5000000000 8328763483207 25000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (849286151/2000000000 : ℝ)^8247 ≤ (31998687747913/100000000000000 : ℝ)^6199 := by
    have hnat : (849286151 : ℕ)^8247*100000000000000^6199 ≤ 31998687747913^6199*2000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849286151 2000000000 31998687747913 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (902363257/2000000000 : ℝ)^8247 ≤ (17343129155491/50000000000000 : ℝ)^6199 := by
    have hnat : (902363257 : ℕ)^8247*50000000000000^6199 ≤ 17343129155491^6199*2000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902363257 2000000000 17343129155491 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2188540089/5000000000 : ℝ), (849286151/2000000000 : ℝ), (902363257/2000000000 : ℝ)] ![(8328763483207/25000000000000 : ℝ), (31998687747913/100000000000000 : ℝ), (17343129155491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2188540089/5000000000 : ℝ)|^8247 ≤ (8328763483207/25000000000000 : ℝ)^6199
        have hw : |(2188540089/5000000000 : ℝ)|=(2188540089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(849286151/2000000000 : ℝ)|^8247 ≤ (31998687747913/100000000000000 : ℝ)^6199
        have hw : |(849286151/2000000000 : ℝ)|=(849286151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(902363257/2000000000 : ℝ)|^8247 ≤ (17343129155491/50000000000000 : ℝ)^6199
        have hw : |(902363257/2000000000 : ℝ)|=(902363257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s5_4 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1104726493/5000000000 : ℝ)*x 0 + (657745621/1250000000 : ℝ)*x 1 + (5396989549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1104726493/5000000000 : ℝ)^8247 ≤ (2683380572097/20000000000000 : ℝ)^6199 := by
    have hnat : (1104726493 : ℕ)^8247*20000000000000^6199 ≤ 2683380572097^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104726493 5000000000 2683380572097 20000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657745621/1250000000 : ℝ)^8247 ≤ (5320249240633/12500000000000 : ℝ)^6199 := by
    have hnat : (657745621 : ℕ)^8247*12500000000000^6199 ≤ 5320249240633^6199*1250000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657745621 1250000000 5320249240633 12500000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396989549/10000000000 : ℝ)^8247 ≤ (44021103202801/100000000000000 : ℝ)^6199 := by
    have hnat : (5396989549 : ℕ)^8247*100000000000000^6199 ≤ 44021103202801^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396989549 10000000000 44021103202801 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1104726493/5000000000 : ℝ), (657745621/1250000000 : ℝ), (5396989549/10000000000 : ℝ)] ![(2683380572097/20000000000000 : ℝ), (5320249240633/12500000000000 : ℝ), (44021103202801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1104726493/5000000000 : ℝ)|^8247 ≤ (2683380572097/20000000000000 : ℝ)^6199
        have hw : |(-1104726493/5000000000 : ℝ)|=(1104726493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657745621/1250000000 : ℝ)|^8247 ≤ (5320249240633/12500000000000 : ℝ)^6199
        have hw : |(657745621/1250000000 : ℝ)|=(657745621/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396989549/10000000000 : ℝ)|^8247 ≤ (44021103202801/100000000000000 : ℝ)^6199
        have hw : |(5396989549/10000000000 : ℝ)|=(5396989549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s5_5 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531154211/1000000000 : ℝ)*x 0 + (-2142980817/10000000000 : ℝ)*x 1 + (5396989483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531154211/1000000000 : ℝ)^8247 ≤ (67337995141/156250000000 : ℝ)^6199 := by
    have hnat : (531154211 : ℕ)^8247*156250000000^6199 ≤ 67337995141^6199*1000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531154211 1000000000 67337995141 156250000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2142980817/10000000000 : ℝ)^8247 ≤ (12882580614187/100000000000000 : ℝ)^6199 := by
    have hnat : (2142980817 : ℕ)^8247*100000000000000^6199 ≤ 12882580614187^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142980817 10000000000 12882580614187 100000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396989483/10000000000 : ℝ)^8247 ≤ (11005275621653/25000000000000 : ℝ)^6199 := by
    have hnat : (5396989483 : ℕ)^8247*25000000000000^6199 ≤ 11005275621653^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396989483 10000000000 11005275621653 25000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531154211/1000000000 : ℝ), (-2142980817/10000000000 : ℝ), (5396989483/10000000000 : ℝ)] ![(67337995141/156250000000 : ℝ), (12882580614187/100000000000000 : ℝ), (11005275621653/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531154211/1000000000 : ℝ)|^8247 ≤ (67337995141/156250000000 : ℝ)^6199
        have hw : |(531154211/1000000000 : ℝ)|=(531154211/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2142980817/10000000000 : ℝ)|^8247 ≤ (12882580614187/100000000000000 : ℝ)^6199
        have hw : |(-2142980817/10000000000 : ℝ)|=(2142980817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396989483/10000000000 : ℝ)|^8247 ≤ (11005275621653/25000000000000 : ℝ)^6199
        have hw : |(5396989483/10000000000 : ℝ)|=(5396989483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s5_6 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5311542087/10000000000 : ℝ)*x 0 + (2698494761/5000000000 : ℝ)*x 1 + (-2142980793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311542087/10000000000 : ℝ)^8247 ≤ (10774079160493/25000000000000 : ℝ)^6199 := by
    have hnat : (5311542087 : ℕ)^8247*25000000000000^6199 ≤ 10774079160493^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311542087 10000000000 10774079160493 25000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698494761/5000000000 : ℝ)^8247 ≤ (22010551454907/50000000000000 : ℝ)^6199 := by
    have hnat : (2698494761 : ℕ)^8247*50000000000000^6199 ≤ 22010551454907^6199*5000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698494761 5000000000 22010551454907 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2142980793/10000000000 : ℝ)^8247 ≤ (2576516084449/20000000000000 : ℝ)^6199 := by
    have hnat : (2142980793 : ℕ)^8247*20000000000000^6199 ≤ 2576516084449^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142980793 10000000000 2576516084449 20000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311542087/10000000000 : ℝ), (2698494761/5000000000 : ℝ), (-2142980793/10000000000 : ℝ)] ![(10774079160493/25000000000000 : ℝ), (22010551454907/50000000000000 : ℝ), (2576516084449/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311542087/10000000000 : ℝ)|^8247 ≤ (10774079160493/25000000000000 : ℝ)^6199
        have hw : |(5311542087/10000000000 : ℝ)|=(5311542087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698494761/5000000000 : ℝ)|^8247 ≤ (22010551454907/50000000000000 : ℝ)^6199
        have hw : |(2698494761/5000000000 : ℝ)|=(2698494761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2142980793/10000000000 : ℝ)|^8247 ≤ (2576516084449/20000000000000 : ℝ)^6199
        have hw : |(-2142980793/10000000000 : ℝ)|=(2142980793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1054_s5_7 (p : ℝ) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (547136429/1250000000 : ℝ)*x 0 + (4511124363/10000000000 : ℝ)*x 1 + (424712527/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (547136429/1250000000 : ℝ)^8247 ≤ (333151678889/1000000000000 : ℝ)^6199 := by
    have hnat : (547136429 : ℕ)^8247*1000000000000^6199 ≤ 333151678889^6199*1250000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      547136429 1250000000 333151678889 1000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4511124363/10000000000 : ℝ)^8247 ≤ (17339590840063/50000000000000 : ℝ)^6199 := by
    have hnat : (4511124363 : ℕ)^8247*50000000000000^6199 ≤ 17339590840063^6199*10000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4511124363 10000000000 17339590840063 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424712527/1000000000 : ℝ)^8247 ≤ (16002825209203/50000000000000 : ℝ)^6199 := by
    have hnat : (424712527 : ℕ)^8247*50000000000000^6199 ≤ 16002825209203^6199*1000000000^8247 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424712527 1000000000 16002825209203 50000000000000 8247 6199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8247/2048 : ℝ)) 8247 6199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(547136429/1250000000 : ℝ), (4511124363/10000000000 : ℝ), (424712527/1000000000 : ℝ)] ![(333151678889/1000000000000 : ℝ), (17339590840063/50000000000000 : ℝ), (16002825209203/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(547136429/1250000000 : ℝ)|^8247 ≤ (333151678889/1000000000000 : ℝ)^6199
        have hw : |(547136429/1250000000 : ℝ)|=(547136429/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4511124363/10000000000 : ℝ)|^8247 ≤ (17339590840063/50000000000000 : ℝ)^6199
        have hw : |(4511124363/10000000000 : ℝ)|=(4511124363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(424712527/1000000000 : ℝ)|^8247 ≤ (16002825209203/50000000000000 : ℝ)^6199
        have hw : |(424712527/1000000000 : ℝ)|=(424712527/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1054_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2849/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2749/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11179/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7027/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2849/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2749/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2849/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2749/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2849/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2749/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2849/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2749/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2849/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2749/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2849/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2749/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2749/25000 : ℝ) ^ (4123/1024 : ℝ) ≤ (344825194420827/2500000000000000000 : ℝ) := by
    have hpowers : (2749/25000 : ℝ)^4123 ≤ (344825194420827/2500000000000000000 : ℝ)^1024 := by
      have hnat : (2749 : ℕ)^4123*2500000000000000000^1024 ≤ 344825194420827^1024*25000^4123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2749 25000 344825194420827 2500000000000000000 4123 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2749/25000 : ℝ)) (X := (344825194420827/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2849/20000 : ℝ) ^ (4123/1024 : ℝ) ≤ (611159123734697/1562500000000000000 : ℝ) := by
    have hpowers : (2849/20000 : ℝ)^4123 ≤ (611159123734697/1562500000000000000 : ℝ)^1024 := by
      have hnat : (2849 : ℕ)^4123*1562500000000000000^1024 ≤ 611159123734697^1024*20000^4123 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2849 20000 611159123734697 1562500000000000000 4123 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2849/20000 : ℝ)) (X := (611159123734697/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250344825194420827/1250000000000000000 : ℝ) ≤ (10000685063105139/10000000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (1250344825194420827/1250000000000000000 : ℝ)^1024 ≤ (10000685063105139/10000000000000000 : ℝ)^4123 := by
      have hnat : (1250344825194420827 : ℕ)^1024*10000000000000000^4123 ≤ 10000685063105139^4123*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250344825194420827 1250000000000000000 10000685063105139 10000000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000685063105139/10000000000000000 : ℝ)) (X := (1250344825194420827/1250000000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506613398961981711/12500000000000000000 : ℝ) ≤ (2000262751372027/2000000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (12506613398961981711/12500000000000000000 : ℝ)^1024 ≤ (2000262751372027/2000000000000000 : ℝ)^4123 := by
      have hnat : (12506613398961981711 : ℕ)^1024*2000000000000000^4123 ≤ 2000262751372027^4123*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506613398961981711 12500000000000000000 2000262751372027 2000000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000262751372027/2000000000000000 : ℝ)) (X := (12506613398961981711/12500000000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (781861159123734697/781250000000000000 : ℝ) ≤ (10001942450615131/10000000000000000 : ℝ) ^ (4123/1024 : ℝ) := by
    have hpowers : (781861159123734697/781250000000000000 : ℝ)^1024 ≤ (10001942450615131/10000000000000000 : ℝ)^4123 := by
      have hnat : (781861159123734697 : ℕ)^1024*10000000000000000^4123 ≤ 10001942450615131^4123*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781861159123734697 781250000000000000 10001942450615131 10000000000000000 1024 4123 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001942450615131/10000000000000000 : ℝ)) (X := (781861159123734697/781250000000000000 : ℝ)) (by norm_num) 4123 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(344825194420827/2500000000000000000 : ℝ) ≤ ((32478399536968724579/32490000000000000000 : ℝ)+2*(157173438749/81225000000000 : ℝ)*(2749/25000 : ℝ))^(4123/1024 : ℝ) := by
    rw [show (32478399536968724579/32490000000000000000 : ℝ)+2*(157173438749/81225000000000 : ℝ)*(2749/25000 : ℝ)=(10000685063105139/10000000000000000 : ℝ) by norm_num, show 1+2*(344825194420827/2500000000000000000 : ℝ)=(1250344825194420827/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(611159123734697/1562500000000000000 : ℝ)+(344825194420827/2500000000000000000 : ℝ) ≤ ((32478399536968724579/32490000000000000000 : ℝ)+(157173438749/81225000000000 : ℝ)*((2849/20000 : ℝ)+(2749/25000 : ℝ)))^(4123/1024 : ℝ) := by
    rw [show (32478399536968724579/32490000000000000000 : ℝ)+(157173438749/81225000000000 : ℝ)*((2849/20000 : ℝ)+(2749/25000 : ℝ))=(2000262751372027/2000000000000000 : ℝ) by norm_num, show 1+(611159123734697/1562500000000000000 : ℝ)+(344825194420827/2500000000000000000 : ℝ)=(12506613398961981711/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(611159123734697/1562500000000000000 : ℝ) ≤ ((32478399536968724579/32490000000000000000 : ℝ)+2*(157173438749/81225000000000 : ℝ)*(2849/20000 : ℝ))^(4123/1024 : ℝ) := by
    rw [show (32478399536968724579/32490000000000000000 : ℝ)+2*(157173438749/81225000000000 : ℝ)*(2849/20000 : ℝ)=(10001942450615131/10000000000000000 : ℝ) by norm_num, show 1+2*(611159123734697/1562500000000000000 : ℝ)=(781861159123734697/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (32478399536968724579/32490000000000000000 : ℝ)*(X 1 0+X 2 0)+(157173438749/81225000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (2749/25000 : ℝ)) (hi := (2849/20000 : ℝ)) (c := (32478399536968724579/32490000000000000000 : ℝ)) (alpha := (157173438749/81225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (32478399536968724579/32490000000000000000 : ℝ)*(X 0 1+X 2 1)+(157173438749/81225000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (2749/25000 : ℝ)) (hi := (2849/20000 : ℝ)) (c := (32478399536968724579/32490000000000000000 : ℝ)) (alpha := (157173438749/81225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (32478399536968724579/32490000000000000000 : ℝ)*(X 0 2+X 1 2)+(157173438749/81225000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4123/1024 : ℝ)) (lo := (2749/25000 : ℝ)) (hi := (2849/20000 : ℝ)) (c := (32478399536968724579/32490000000000000000 : ℝ)) (alpha := (157173438749/81225000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2209447271/10000000000 : ℝ)*X 0 0+(269867233/500000000 : ℝ)*X 0 1+(2630805577/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345697503/10000000000 : ℝ)*X 1 0+(-2278359117/10000000000 : ℝ)*X 1 1+(328850691/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345697373/10000000000 : ℝ)*X 2 0+(5261611159/10000000000 : ℝ)*X 2 1+(-2278359153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2188540089/5000000000 : ℝ)*X 0 0+(849286151/2000000000 : ℝ)*X 0 1+(902363257/2000000000 : ℝ)*X 0 2+(2188540089/5000000000 : ℝ)*X 1 0+(849286151/2000000000 : ℝ)*X 1 1+(902363257/2000000000 : ℝ)*X 1 2+(2188540089/5000000000 : ℝ)*X 2 0+(849286151/2000000000 : ℝ)*X 2 1+(902363257/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1104726493/5000000000 : ℝ)*X 0 0+(657745621/1250000000 : ℝ)*X 0 1+(5396989549/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531154211/1000000000 : ℝ)*X 1 0+(-2142980817/10000000000 : ℝ)*X 1 1+(5396989483/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311542087/10000000000 : ℝ)*X 2 0+(2698494761/5000000000 : ℝ)*X 2 1+(-2142980793/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((547136429/1250000000 : ℝ)*X 0 0+(4511124363/10000000000 : ℝ)*X 0 1+(424712527/1000000000 : ℝ)*X 0 2+(547136429/1250000000 : ℝ)*X 1 0+(4511124363/10000000000 : ℝ)*X 1 1+(424712527/1000000000 : ℝ)*X 1 2+(547136429/1250000000 : ℝ)*X 2 0+(4511124363/10000000000 : ℝ)*X 2 1+(424712527/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1054_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (262175832303181595845174233/45125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (233955621/20000000000000 : ℝ)*(base19) + (459759989/50000000000000 : ℝ)*(base23) + (68941881/100000000000000 : ℝ)*(lower2) + (142334697/100000000000000 : ℝ)*(upper3) + (15469049/50000000000000 : ℝ)*(lower4) + (2783893067045719/50000000000000 : ℝ)*(major0) + (2783893067045719/50000000000000 : ℝ)*(major1) + (2783893067045719/50000000000000 : ℝ)*(major2) + (1841852491824887/25000000000000 : ℝ)*(sp0) + (7367433893904459/100000000000000 : ℝ)*(sp1) + (3683717072081293/50000000000000 : ℝ)*(sp2) + (75362376561453/2000000000000 : ℝ)*(sp3) + (5019276603/20000000000000 : ℝ)*(sp4) + (18182761293/100000000000000 : ℝ)*(sp7) + (471017126354243/12500000000000 : ℝ)*(f.failure) + (1841858765920641/25000000000000 : ℝ)*(f.sum) + (26010875266681/8122500000000000000000000000 : ℝ)*base66 + (39074815713153927301/1624500000000000000000000000000000 : ℝ)*base67 + (388024528242927301/1624500000000000000000000000000000 : ℝ)*base69 + (20410759520924072699/1624500000000000000000000000000000 : ℝ)*base72 + (32312553811889/8122500000000000000000000000 : ℝ)*base73 + (23439630668156427301/1624500000000000000000000000000000 : ℝ)*base75 + (18791315950301427301/1624500000000000000000000000000000 : ℝ)*base77 + (8616309862890927301/1624500000000000000000000000000000 : ℝ)*base79 + (8849029592371/8122500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (149141/312500000000000000000 : ℝ)*base90 + (149141/312500000000000000000 : ℝ)*base92 + (149141/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (883125391828423327906930897/90250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (692933227/50000000000000 : ℝ)*(base19) + (427266857/25000000000000 : ℝ)*(base23) + (126438253/100000000000000 : ℝ)*(upper3) + (79890609/50000000000000 : ℝ)*(lower4) + (147245711/100000000000000 : ℝ)*(upper5) + (2798486517331871/50000000000000 : ℝ)*(major0) + (2798486517331871/50000000000000 : ℝ)*(major1) + (2798486517331871/50000000000000 : ℝ)*(major2) + (17085350083/50000000000000 : ℝ)*(sp1) + (1705547243/4000000000000 : ℝ)*(sp2) + (1851513943820667/25000000000000 : ℝ)*(sp4) + (7406020218716047/100000000000000 : ℝ)*(sp5) + (1481202285506833/20000000000000 : ℝ)*(sp6) + (946972491966843/25000000000000 : ℝ)*(sp7) + (946972491966843/25000000000000 : ℝ)*(f.failure) + (1851513943820667/25000000000000 : ℝ)*(f.sum) + (1491666331543/1015312500000000000000000000 : ℝ)*base66 + (20314889183519357309/1624500000000000000000000000000000 : ℝ)*base67 + (3350611735775357309/1624500000000000000000000000000000 : ℝ)*base69 + (5178411087875357309/1624500000000000000000000000000000 : ℝ)*base71 + (58584996062357/16245000000000000000000000000 : ℝ)*base73 + (10282407128717142691/1624500000000000000000000000000000 : ℝ)*base76 + (14184156566043642691/1624500000000000000000000000000000 : ℝ)*base78 + (35340603763359857309/1624500000000000000000000000000000 : ℝ)*base79 + (2237988498301/507656250000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (8195341/625000000000000000000 : ℝ)*base90 + (8195341/625000000000000000000 : ℝ)*base92 + (8195341/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1054_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2849/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2749/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11179/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1054_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1054_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16781/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8653/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11179/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1054_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1054_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1054_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4123/1024 : ℝ) ≤ p) (hpb : p ≤ (8247/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (36939913/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16781/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8653/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11179/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7027/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1054_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
