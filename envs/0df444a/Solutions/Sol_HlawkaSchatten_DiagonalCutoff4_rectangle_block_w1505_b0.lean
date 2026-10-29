-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1505_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:53:41.859825+00:00
-- url     : https://prove2.me/submissions/135e9ca3-40c2-44f6-bd5b-5924ff75b969

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
theorem support_rectangle_w1505_s0_0 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-423320849/2500000000 : ℝ)*x 0 + (591823851/1000000000 : ℝ)*x 1 + (606538961/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (423320849/2500000000 : ℝ)^4507 ≤ (10045616849989/100000000000000 : ℝ)^3483 := by
    have hnat : (423320849 : ℕ)^4507*100000000000000^3483 ≤ 10045616849989^3483*2500000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423320849 2500000000 10045616849989 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (591823851/1000000000 : ℝ)^4507 ≤ (6340553797303/12500000000000 : ℝ)^3483 := by
    have hnat : (591823851 : ℕ)^4507*12500000000000^3483 ≤ 6340553797303^3483*1000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      591823851 1000000000 6340553797303 12500000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (606538961/1250000000 : ℝ)^4507 ≤ (19614976380053/50000000000000 : ℝ)^3483 := by
    have hnat : (606538961 : ℕ)^4507*50000000000000^3483 ≤ 19614976380053^3483*1250000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      606538961 1250000000 19614976380053 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-423320849/2500000000 : ℝ), (591823851/1000000000 : ℝ), (606538961/1250000000 : ℝ)] ![(10045616849989/100000000000000 : ℝ), (6340553797303/12500000000000 : ℝ), (19614976380053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-423320849/2500000000 : ℝ)|^4507 ≤ (10045616849989/100000000000000 : ℝ)^3483
        have hw : |(-423320849/2500000000 : ℝ)|=(423320849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(591823851/1000000000 : ℝ)|^4507 ≤ (6340553797303/12500000000000 : ℝ)^3483
        have hw : |(591823851/1000000000 : ℝ)|=(591823851/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(606538961/1250000000 : ℝ)|^4507 ≤ (19614976380053/50000000000000 : ℝ)^3483
        have hw : |(606538961/1250000000 : ℝ)|=(606538961/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s0_1 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1369876253/2500000000 : ℝ)*x 0 + (-2291296767/10000000000 : ℝ)*x 1 + (151634739/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1369876253/2500000000 : ℝ)^4507 ≤ (22956275782189/50000000000000 : ℝ)^3483 := by
    have hnat : (1369876253 : ℕ)^4507*50000000000000^3483 ≤ 22956275782189^3483*2500000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369876253 2500000000 22956275782189 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2291296767/10000000000 : ℝ)^4507 ≤ (118859968659/800000000000 : ℝ)^3483 := by
    have hnat : (2291296767 : ℕ)^4507*800000000000^3483 ≤ 118859968659^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2291296767 10000000000 118859968659 800000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (151634739/312500000 : ℝ)^4507 ≤ (39229952341637/100000000000000 : ℝ)^3483 := by
    have hnat : (151634739 : ℕ)^4507*100000000000000^3483 ≤ 39229952341637^3483*312500000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151634739 312500000 39229952341637 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1369876253/2500000000 : ℝ), (-2291296767/10000000000 : ℝ), (151634739/312500000 : ℝ)] ![(22956275782189/50000000000000 : ℝ), (118859968659/800000000000 : ℝ), (39229952341637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1369876253/2500000000 : ℝ)|^4507 ≤ (22956275782189/50000000000000 : ℝ)^3483
        have hw : |(1369876253/2500000000 : ℝ)|=(1369876253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2291296767/10000000000 : ℝ)|^4507 ≤ (118859968659/800000000000 : ℝ)^3483
        have hw : |(-2291296767/10000000000 : ℝ)|=(2291296767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(151634739/312500000 : ℝ)|^4507 ≤ (39229952341637/100000000000000 : ℝ)^3483
        have hw : |(151634739/312500000 : ℝ)|=(151634739/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s0_2 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2739752523/5000000000 : ℝ)*x 0 + (1213077913/2500000000 : ℝ)*x 1 + (-2291296717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2739752523/5000000000 : ℝ)^4507 ≤ (45912551933019/100000000000000 : ℝ)^3483 := by
    have hnat : (2739752523 : ℕ)^4507*100000000000000^3483 ≤ 45912551933019^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2739752523 5000000000 45912551933019 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1213077913/2500000000 : ℝ)^4507 ≤ (9807488095871/25000000000000 : ℝ)^3483 := by
    have hnat : (1213077913 : ℕ)^4507*25000000000000^3483 ≤ 9807488095871^3483*2500000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1213077913 2500000000 9807488095871 25000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2291296717/10000000000 : ℝ)^4507 ≤ (371437391571/2500000000000 : ℝ)^3483 := by
    have hnat : (2291296717 : ℕ)^4507*2500000000000^3483 ≤ 371437391571^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2291296717 10000000000 371437391571 2500000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2739752523/5000000000 : ℝ), (1213077913/2500000000 : ℝ), (-2291296717/10000000000 : ℝ)] ![(45912551933019/100000000000000 : ℝ), (9807488095871/25000000000000 : ℝ), (371437391571/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2739752523/5000000000 : ℝ)|^4507 ≤ (45912551933019/100000000000000 : ℝ)^3483
        have hw : |(2739752523/5000000000 : ℝ)|=(2739752523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1213077913/2500000000 : ℝ)|^4507 ≤ (9807488095871/25000000000000 : ℝ)^3483
        have hw : |(1213077913/2500000000 : ℝ)|=(1213077913/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2291296717/10000000000 : ℝ)|^4507 ≤ (371437391571/2500000000000 : ℝ)^3483
        have hw : |(-2291296717/10000000000 : ℝ)|=(2291296717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s0_3 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (829407307/2000000000 : ℝ)*x 0 + (3091234307/10000000000 : ℝ)*x 1 + (1099279337/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (829407307/2000000000 : ℝ)^4507 ≤ (32014963590263/100000000000000 : ℝ)^3483 := by
    have hnat : (829407307 : ℕ)^4507*100000000000000^3483 ≤ 32014963590263^3483*2000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829407307 2000000000 32014963590263 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3091234307/10000000000 : ℝ)^4507 ≤ (21889256140287/100000000000000 : ℝ)^3483 := by
    have hnat : (3091234307 : ℕ)^4507*100000000000000^3483 ≤ 21889256140287^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3091234307 10000000000 21889256140287 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1099279337/2000000000 : ℝ)^4507 ≤ (46095780249811/100000000000000 : ℝ)^3483 := by
    have hnat : (1099279337 : ℕ)^4507*100000000000000^3483 ≤ 46095780249811^3483*2000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099279337 2000000000 46095780249811 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(829407307/2000000000 : ℝ), (3091234307/10000000000 : ℝ), (1099279337/2000000000 : ℝ)] ![(32014963590263/100000000000000 : ℝ), (21889256140287/100000000000000 : ℝ), (46095780249811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(829407307/2000000000 : ℝ)|^4507 ≤ (32014963590263/100000000000000 : ℝ)^3483
        have hw : |(829407307/2000000000 : ℝ)|=(829407307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3091234307/10000000000 : ℝ)|^4507 ≤ (21889256140287/100000000000000 : ℝ)^3483
        have hw : |(3091234307/10000000000 : ℝ)|=(3091234307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1099279337/2000000000 : ℝ)|^4507 ≤ (46095780249811/100000000000000 : ℝ)^3483
        have hw : |(1099279337/2000000000 : ℝ)|=(1099279337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s0_4 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-21210801/125000000 : ℝ)*x 0 + (2439768229/5000000000 : ℝ)*x 1 + (736254689/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21210801/125000000 : ℝ)^4507 ≤ (5036556818579/50000000000000 : ℝ)^3483 := by
    have hnat : (21210801 : ℕ)^4507*50000000000000^3483 ≤ 5036556818579^3483*125000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21210801 125000000 5036556818579 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2439768229/5000000000 : ℝ)^4507 ≤ (77177744799/195312500000 : ℝ)^3483 := by
    have hnat : (2439768229 : ℕ)^4507*195312500000^3483 ≤ 77177744799^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2439768229 5000000000 77177744799 195312500000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (736254689/1250000000 : ℝ)^4507 ≤ (24615176277/48828125000 : ℝ)^3483 := by
    have hnat : (736254689 : ℕ)^4507*48828125000^3483 ≤ 24615176277^3483*1250000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      736254689 1250000000 24615176277 48828125000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-21210801/125000000 : ℝ), (2439768229/5000000000 : ℝ), (736254689/1250000000 : ℝ)] ![(5036556818579/50000000000000 : ℝ), (77177744799/195312500000 : ℝ), (24615176277/48828125000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-21210801/125000000 : ℝ)|^4507 ≤ (5036556818579/50000000000000 : ℝ)^3483
        have hw : |(-21210801/125000000 : ℝ)|=(21210801/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2439768229/5000000000 : ℝ)|^4507 ≤ (77177744799/195312500000 : ℝ)^3483
        have hw : |(2439768229/5000000000 : ℝ)|=(2439768229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(736254689/1250000000 : ℝ)|^4507 ≤ (24615176277/48828125000 : ℝ)^3483
        have hw : |(736254689/1250000000 : ℝ)|=(736254689/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s0_5 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (648539407/1250000000 : ℝ)*x 0 + (-1253570847/10000000000 : ℝ)*x 1 + (2945018781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (648539407/1250000000 : ℝ)^4507 ≤ (21390171867009/50000000000000 : ℝ)^3483 := by
    have hnat : (648539407 : ℕ)^4507*50000000000000^3483 ≤ 21390171867009^3483*1250000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648539407 1250000000 21390171867009 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1253570847/10000000000 : ℝ)^4507 ≤ (3403887340129/50000000000000 : ℝ)^3483 := by
    have hnat : (1253570847 : ℕ)^4507*50000000000000^3483 ≤ 3403887340129^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1253570847 10000000000 3403887340129 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2945018781/5000000000 : ℝ)^4507 ≤ (12602970392263/25000000000000 : ℝ)^3483 := by
    have hnat : (2945018781 : ℕ)^4507*25000000000000^3483 ≤ 12602970392263^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2945018781 5000000000 12602970392263 25000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(648539407/1250000000 : ℝ), (-1253570847/10000000000 : ℝ), (2945018781/5000000000 : ℝ)] ![(21390171867009/50000000000000 : ℝ), (3403887340129/50000000000000 : ℝ), (12602970392263/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(648539407/1250000000 : ℝ)|^4507 ≤ (21390171867009/50000000000000 : ℝ)^3483
        have hw : |(648539407/1250000000 : ℝ)|=(648539407/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1253570847/10000000000 : ℝ)|^4507 ≤ (3403887340129/50000000000000 : ℝ)^3483
        have hw : |(-1253570847/10000000000 : ℝ)|=(1253570847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2945018781/5000000000 : ℝ)|^4507 ≤ (12602970392263/25000000000000 : ℝ)^3483
        have hw : |(2945018781/5000000000 : ℝ)|=(2945018781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s0_6 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2594157631/5000000000 : ℝ)*x 0 + (736254693/1250000000 : ℝ)*x 1 + (-1253570867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2594157631/5000000000 : ℝ)^4507 ≤ (10695085949509/25000000000000 : ℝ)^3483 := by
    have hnat : (2594157631 : ℕ)^4507*25000000000000^3483 ≤ 10695085949509^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2594157631 5000000000 10695085949509 25000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (736254693/1250000000 : ℝ)^4507 ≤ (504118813697/1000000000000 : ℝ)^3483 := by
    have hnat : (736254693 : ℕ)^4507*1000000000000^3483 ≤ 504118813697^3483*1250000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      736254693 1250000000 504118813697 1000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1253570867/10000000000 : ℝ)^4507 ≤ (1701943705201/25000000000000 : ℝ)^3483 := by
    have hnat : (1253570867 : ℕ)^4507*25000000000000^3483 ≤ 1701943705201^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1253570867 10000000000 1701943705201 25000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2594157631/5000000000 : ℝ), (736254693/1250000000 : ℝ), (-1253570867/10000000000 : ℝ)] ![(10695085949509/25000000000000 : ℝ), (504118813697/1000000000000 : ℝ), (1701943705201/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2594157631/5000000000 : ℝ)|^4507 ≤ (10695085949509/25000000000000 : ℝ)^3483
        have hw : |(2594157631/5000000000 : ℝ)|=(2594157631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(736254693/1250000000 : ℝ)|^4507 ≤ (504118813697/1000000000000 : ℝ)^3483
        have hw : |(736254693/1250000000 : ℝ)|=(736254693/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1253570867/10000000000 : ℝ)|^4507 ≤ (1701943705201/25000000000000 : ℝ)^3483
        have hw : |(-1253570867/10000000000 : ℝ)|=(1253570867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s0_7 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (415511611/1000000000 : ℝ)*x 0 + (217398659/400000000 : ℝ)*x 1 + (3154867289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (415511611/1000000000 : ℝ)^4507 ≤ (1604784931437/5000000000000 : ℝ)^3483 := by
    have hnat : (415511611 : ℕ)^4507*5000000000000^3483 ≤ 1604784931437^3483*1000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415511611 1000000000 1604784931437 5000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (217398659/400000000 : ℝ)^4507 ≤ (177461821923/390625000000 : ℝ)^3483 := by
    have hnat : (217398659 : ℕ)^4507*390625000000^3483 ≤ 177461821923^3483*400000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217398659 400000000 177461821923 390625000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154867289/10000000000 : ℝ)^4507 ≤ (22474074947307/100000000000000 : ℝ)^3483 := by
    have hnat : (3154867289 : ℕ)^4507*100000000000000^3483 ≤ 22474074947307^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154867289 10000000000 22474074947307 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(415511611/1000000000 : ℝ), (217398659/400000000 : ℝ), (3154867289/10000000000 : ℝ)] ![(1604784931437/5000000000000 : ℝ), (177461821923/390625000000 : ℝ), (22474074947307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(415511611/1000000000 : ℝ)|^4507 ≤ (1604784931437/5000000000000 : ℝ)^3483
        have hw : |(415511611/1000000000 : ℝ)|=(415511611/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(217398659/400000000 : ℝ)|^4507 ≤ (177461821923/390625000000 : ℝ)^3483
        have hw : |(217398659/400000000 : ℝ)|=(217398659/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154867289/10000000000 : ℝ)|^4507 ≤ (22474074947307/100000000000000 : ℝ)^3483
        have hw : |(3154867289/10000000000 : ℝ)|=(3154867289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1505_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162820231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2737/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1023/4000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4505/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4505 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4505*1^1024 ≤ 0^1024*1^4505 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4505 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4505/1024 : ℝ) ≤ (355080747511806373/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4505 ≤ (355080747511806373/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4505*20000000000000000000^1024 ≤ 355080747511806373^1024*5^4505 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 355080747511806373 20000000000000000000 4505 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (355080747511806373/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4505/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4505 := by
      have hnat : (1 : ℕ)^1024*1^4505 ≤ 1^4505*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4505 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20355080747511806373/20000000000000000000 : ℝ) ≤ (313752547489319/312500000000000 : ℝ) ^ (4505/1024 : ℝ) := by
    have hpowers : (20355080747511806373/20000000000000000000 : ℝ)^1024 ≤ (313752547489319/312500000000000 : ℝ)^4505 := by
      have hnat : (20355080747511806373 : ℕ)^1024*312500000000000^4505 ≤ 313752547489319^4505*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20355080747511806373 20000000000000000000 313752547489319 312500000000000 1024 4505 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (313752547489319/312500000000000 : ℝ)) (X := (20355080747511806373/20000000000000000000 : ℝ)) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10355080747511806373/10000000000000000000 : ℝ) ≤ (157502547489319/156250000000000 : ℝ) ^ (4505/1024 : ℝ) := by
    have hpowers : (10355080747511806373/10000000000000000000 : ℝ)^1024 ≤ (157502547489319/156250000000000 : ℝ)^4505 := by
      have hnat : (10355080747511806373 : ℕ)^1024*156250000000000^4505 ≤ 157502547489319^4505*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10355080747511806373 10000000000000000000 157502547489319 156250000000000 1024 4505 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (157502547489319/156250000000000 : ℝ)) (X := (10355080747511806373/10000000000000000000 : ℝ)) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1252547489319/125000000000000 : ℝ)*(0 : ℝ))^(4505/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1252547489319/125000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(355080747511806373/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1252547489319/125000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4505/1024 : ℝ) := by
    rw [show (1 : ℝ)+(1252547489319/125000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(313752547489319/312500000000000 : ℝ) by norm_num, show 1+(355080747511806373/20000000000000000000 : ℝ)+(0 : ℝ)=(20355080747511806373/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(355080747511806373/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1252547489319/125000000000000 : ℝ)*(2/5 : ℝ))^(4505/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(1252547489319/125000000000000 : ℝ)*(2/5 : ℝ)=(157502547489319/156250000000000 : ℝ) by norm_num, show 1+2*(355080747511806373/20000000000000000000 : ℝ)=(10355080747511806373/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1252547489319/125000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4505/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1252547489319/125000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1252547489319/125000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4505/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1252547489319/125000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1252547489319/125000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4505/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1252547489319/125000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-423320849/2500000000 : ℝ)*X 0 0+(591823851/1000000000 : ℝ)*X 0 1+(606538961/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1369876253/2500000000 : ℝ)*X 1 0+(-2291296767/10000000000 : ℝ)*X 1 1+(151634739/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2739752523/5000000000 : ℝ)*X 2 0+(1213077913/2500000000 : ℝ)*X 2 1+(-2291296717/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((829407307/2000000000 : ℝ)*X 0 0+(3091234307/10000000000 : ℝ)*X 0 1+(1099279337/2000000000 : ℝ)*X 0 2+(829407307/2000000000 : ℝ)*X 1 0+(3091234307/10000000000 : ℝ)*X 1 1+(1099279337/2000000000 : ℝ)*X 1 2+(829407307/2000000000 : ℝ)*X 2 0+(3091234307/10000000000 : ℝ)*X 2 1+(1099279337/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-21210801/125000000 : ℝ)*X 0 0+(2439768229/5000000000 : ℝ)*X 0 1+(736254689/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((648539407/1250000000 : ℝ)*X 1 0+(-1253570847/10000000000 : ℝ)*X 1 1+(2945018781/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2594157631/5000000000 : ℝ)*X 2 0+(736254693/1250000000 : ℝ)*X 2 1+(-1253570867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((415511611/1000000000 : ℝ)*X 0 0+(217398659/400000000 : ℝ)*X 0 1+(3154867289/10000000000 : ℝ)*X 0 2+(415511611/1000000000 : ℝ)*X 1 0+(217398659/400000000 : ℝ)*X 1 1+(3154867289/10000000000 : ℝ)*X 1 2+(415511611/1000000000 : ℝ)*X 2 0+(217398659/400000000 : ℝ)*X 2 1+(3154867289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11440310982682703346399/3125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3127207/10000000000000 : ℝ)*(base1) + (418381653/50000000000000 : ℝ)*(base19) + (421292253/50000000000000 : ℝ)*(base23) + (49665813/50000000000000 : ℝ)*(upper3) + (114992329/100000000000000 : ℝ)*(upper5) + (338482877366631/50000000000000 : ℝ)*(major0) + (338482877366631/50000000000000 : ℝ)*(major1) + (338482877366631/50000000000000 : ℝ)*(major2) + (938153444781351/100000000000000 : ℝ)*(sp0) + (938155587957899/100000000000000 : ℝ)*(sp1) + (9381555821367/1000000000000 : ℝ)*(sp2) + (415773623840339/100000000000000 : ℝ)*(sp3) + (752802981/25000000000000 : ℝ)*(sp4) + (32690073/2500000000000 : ℝ)*(sp7) + (415774962715329/100000000000000 : ℝ)*(f.failure) + (469078212360603/50000000000000 : ℝ)*(f.sum) + (1040161253459/781250000000000000000000000 : ℝ)*base66 + (21130761545539/6250000000000000000000000000 : ℝ)*base67 + (41121921570539/6250000000000000000000000000 : ℝ)*base69 + (9439842308039/6250000000000000000000000000 : ℝ)*base71 + (1789930326789/3125000000000000000000000000 : ℝ)*base73 + (35822646720539/6250000000000000000000000000 : ℝ)*base75 + (5087977233039/6250000000000000000000000000 : ℝ)*base77 + (19659714691961/6250000000000000000000000000 : ℝ)*base80 + (5123181327457/1562500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (55020999/10000000000000000000000 : ℝ)*base89 + (55020999/10000000000000000000000 : ℝ)*base91 + (55020999/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4168196833070799968211/781250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1196762449/100000000000000 : ℝ)*(base19) + (603546827/50000000000000 : ℝ)*(base23) + (77471931/100000000000000 : ℝ)*(base32) + (180588049/100000000000000 : ℝ)*(upper3) + (12693533/10000000000000 : ℝ)*(upper5) + (89261573141001/12500000000000 : ℝ)*(major0) + (89261573141001/12500000000000 : ℝ)*(major1) + (89261573141001/12500000000000 : ℝ)*(major2) + (3047286921/100000000000000 : ℝ)*(sp1) + (3210973361/100000000000000 : ℝ)*(sp2) + (494803842473999/50000000000000 : ℝ)*(sp4) + (989603440898627/100000000000000 : ℝ)*(sp5) + (989603266880983/100000000000000 : ℝ)*(sp6) + (54822153749127/12500000000000 : ℝ)*(sp7) + (109644326866237/25000000000000 : ℝ)*(f.failure) + (494803842473999/50000000000000 : ℝ)*(f.sum) + (2044378530819/781250000000000000000000000 : ℝ)*base65 + (3848999162931/1562500000000000000000000000 : ℝ)*base68 + (296461905819/1562500000000000000000000000 : ℝ)*base69 + (2106717350431/1562500000000000000000000000 : ℝ)*base72 + (1627286451347/390625000000000000000000000 : ℝ)*base73 + (111046225921/24414062500000000000000000 : ℝ)*base75 + (2063655769181/1562500000000000000000000000 : ℝ)*base78 + (6062150787931/1562500000000000000000000000 : ℝ)*base80 + (7677820177263/1562500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (14440747/2500000000000000000000 : ℝ)*base89 + (14440747/2500000000000000000000 : ℝ)*base91 + (14440747/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1505_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162820231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2737/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1023/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1505_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1505_s1_0 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-57777407/312500000 : ℝ)*x 0 + (1115041493/2000000000 : ℝ)*x 1 + (2547685297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (57777407/312500000 : ℝ)^4507 ≤ (11255878744579/100000000000000 : ℝ)^3483 := by
    have hnat : (57777407 : ℕ)^4507*100000000000000^3483 ≤ 11255878744579^3483*312500000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57777407 312500000 11255878744579 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1115041493/2000000000 : ℝ)^4507 ≤ (46952846075417/100000000000000 : ℝ)^3483 := by
    have hnat : (1115041493 : ℕ)^4507*100000000000000^3483 ≤ 46952846075417^3483*2000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115041493 2000000000 46952846075417 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2547685297/5000000000 : ℝ)^4507 ≤ (8358255031847/20000000000000 : ℝ)^3483 := by
    have hnat : (2547685297 : ℕ)^4507*20000000000000^3483 ≤ 8358255031847^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2547685297 5000000000 8358255031847 20000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-57777407/312500000 : ℝ), (1115041493/2000000000 : ℝ), (2547685297/5000000000 : ℝ)] ![(11255878744579/100000000000000 : ℝ), (46952846075417/100000000000000 : ℝ), (8358255031847/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-57777407/312500000 : ℝ)|^4507 ≤ (11255878744579/100000000000000 : ℝ)^3483
        have hw : |(-57777407/312500000 : ℝ)|=(57777407/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1115041493/2000000000 : ℝ)|^4507 ≤ (46952846075417/100000000000000 : ℝ)^3483
        have hw : |(1115041493/2000000000 : ℝ)|=(1115041493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2547685297/5000000000 : ℝ)|^4507 ≤ (8358255031847/20000000000000 : ℝ)^3483
        have hw : |(2547685297/5000000000 : ℝ)|=(2547685297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s1_1 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2693951401/5000000000 : ℝ)*x 0 + (-2101767951/10000000000 : ℝ)*x 1 + (2547683637/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2693951401/5000000000 : ℝ)^4507 ≤ (44921816954261/100000000000000 : ℝ)^3483 := by
    have hnat : (2693951401 : ℕ)^4507*100000000000000^3483 ≤ 44921816954261^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2693951401 5000000000 44921816954261 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2101767951/10000000000 : ℝ)^4507 ≤ (531477724233/4000000000000 : ℝ)^3483 := by
    have hnat : (2101767951 : ℕ)^4507*4000000000000^3483 ≤ 531477724233^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101767951 10000000000 531477724233 4000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2547683637/5000000000 : ℝ)^4507 ≤ (41791239923611/100000000000000 : ℝ)^3483 := by
    have hnat : (2547683637 : ℕ)^4507*100000000000000^3483 ≤ 41791239923611^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2547683637 5000000000 41791239923611 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2693951401/5000000000 : ℝ), (-2101767951/10000000000 : ℝ), (2547683637/5000000000 : ℝ)] ![(44921816954261/100000000000000 : ℝ), (531477724233/4000000000000 : ℝ), (41791239923611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2693951401/5000000000 : ℝ)|^4507 ≤ (44921816954261/100000000000000 : ℝ)^3483
        have hw : |(2693951401/5000000000 : ℝ)|=(2693951401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2101767951/10000000000 : ℝ)|^4507 ≤ (531477724233/4000000000000 : ℝ)^3483
        have hw : |(-2101767951/10000000000 : ℝ)|=(2101767951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2547683637/5000000000 : ℝ)|^4507 ≤ (41791239923611/100000000000000 : ℝ)^3483
        have hw : |(2547683637/5000000000 : ℝ)|=(2547683637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s1_2 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5387902279/10000000000 : ℝ)*x 0 + (1273842163/2500000000 : ℝ)*x 1 + (-2101766853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5387902279/10000000000 : ℝ)^4507 ≤ (22460905655869/50000000000000 : ℝ)^3483 := by
    have hnat : (5387902279 : ℕ)^4507*50000000000000^3483 ≤ 22460905655869^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387902279 10000000000 22460905655869 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1273842163/2500000000 : ℝ)^4507 ≤ (41791254548517/100000000000000 : ℝ)^3483 := by
    have hnat : (1273842163 : ℕ)^4507*100000000000000^3483 ≤ 41791254548517^3483*2500000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1273842163 2500000000 41791254548517 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2101766853/10000000000 : ℝ)^4507 ≤ (10629547299/80000000000 : ℝ)^3483 := by
    have hnat : (2101766853 : ℕ)^4507*80000000000^3483 ≤ 10629547299^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2101766853 10000000000 10629547299 80000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5387902279/10000000000 : ℝ), (1273842163/2500000000 : ℝ), (-2101766853/10000000000 : ℝ)] ![(22460905655869/50000000000000 : ℝ), (41791254548517/100000000000000 : ℝ), (10629547299/80000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5387902279/10000000000 : ℝ)|^4507 ≤ (22460905655869/50000000000000 : ℝ)^3483
        have hw : |(5387902279/10000000000 : ℝ)|=(5387902279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1273842163/2500000000 : ℝ)|^4507 ≤ (41791254548517/100000000000000 : ℝ)^3483
        have hw : |(1273842163/2500000000 : ℝ)|=(1273842163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2101766853/10000000000 : ℝ)|^4507 ≤ (10629547299/80000000000 : ℝ)^3483
        have hw : |(-2101766853/10000000000 : ℝ)|=(2101766853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s1_3 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4252166003/10000000000 : ℝ)*x 0 + (1870036279/5000000000 : ℝ)*x 1 + (3014241/6250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4252166003/10000000000 : ℝ)^4507 ≤ (16534529087227/50000000000000 : ℝ)^3483 := by
    have hnat : (4252166003 : ℕ)^4507*50000000000000^3483 ≤ 16534529087227^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252166003 10000000000 16534529087227 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1870036279/5000000000 : ℝ)^4507 ≤ (7002401519967/25000000000000 : ℝ)^3483 := by
    have hnat : (1870036279 : ℕ)^4507*25000000000000^3483 ≤ 7002401519967^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870036279 5000000000 7002401519967 25000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3014241/6250000 : ℝ)^4507 ≤ (38921335731127/100000000000000 : ℝ)^3483 := by
    have hnat : (3014241 : ℕ)^4507*100000000000000^3483 ≤ 38921335731127^3483*6250000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3014241 6250000 38921335731127 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4252166003/10000000000 : ℝ), (1870036279/5000000000 : ℝ), (3014241/6250000 : ℝ)] ![(16534529087227/50000000000000 : ℝ), (7002401519967/25000000000000 : ℝ), (38921335731127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4252166003/10000000000 : ℝ)|^4507 ≤ (16534529087227/50000000000000 : ℝ)^3483
        have hw : |(4252166003/10000000000 : ℝ)|=(4252166003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1870036279/5000000000 : ℝ)|^4507 ≤ (7002401519967/25000000000000 : ℝ)^3483
        have hw : |(1870036279/5000000000 : ℝ)|=(1870036279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3014241/6250000 : ℝ)|^4507 ≤ (38921335731127/100000000000000 : ℝ)^3483
        have hw : |(3014241/6250000 : ℝ)|=(3014241/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s1_4 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1849193081/10000000000 : ℝ)*x 0 + (2550394107/5000000000 : ℝ)*x 1 + (696212651/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1849193081/10000000000 : ℝ)^4507 ≤ (11258368643921/100000000000000 : ℝ)^3483 := by
    have hnat : (1849193081 : ℕ)^4507*100000000000000^3483 ≤ 11258368643921^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1849193081 10000000000 11258368643921 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2550394107/5000000000 : ℝ)^4507 ≤ (1307774440879/3125000000000 : ℝ)^3483 := by
    have hnat : (2550394107 : ℕ)^4507*3125000000000^3483 ≤ 1307774440879^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2550394107 5000000000 1307774440879 3125000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (696212651/1250000000 : ℝ)^4507 ≤ (46892849234991/100000000000000 : ℝ)^3483 := by
    have hnat : (696212651 : ℕ)^4507*100000000000000^3483 ≤ 46892849234991^3483*1250000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      696212651 1250000000 46892849234991 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1849193081/10000000000 : ℝ), (2550394107/5000000000 : ℝ), (696212651/1250000000 : ℝ)] ![(11258368643921/100000000000000 : ℝ), (1307774440879/3125000000000 : ℝ), (46892849234991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1849193081/10000000000 : ℝ)|^4507 ≤ (11258368643921/100000000000000 : ℝ)^3483
        have hw : |(-1849193081/10000000000 : ℝ)|=(1849193081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2550394107/5000000000 : ℝ)|^4507 ≤ (1307774440879/3125000000000 : ℝ)^3483
        have hw : |(2550394107/5000000000 : ℝ)|=(2550394107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(696212651/1250000000 : ℝ)|^4507 ≤ (46892849234991/100000000000000 : ℝ)^3483
        have hw : |(696212651/1250000000 : ℝ)|=(696212651/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s1_5 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2630811217/5000000000 : ℝ)*x 0 + (-406858533/2500000000 : ℝ)*x 1 + (5569701359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2630811217/5000000000 : ℝ)^4507 ≤ (43564128136933/100000000000000 : ℝ)^3483 := by
    have hnat : (2630811217 : ℕ)^4507*100000000000000^3483 ≤ 43564128136933^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630811217 5000000000 43564128136933 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (406858533/2500000000 : ℝ)^4507 ≤ (4771510488401/50000000000000 : ℝ)^3483 := by
    have hnat : (406858533 : ℕ)^4507*50000000000000^3483 ≤ 4771510488401^3483*2500000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      406858533 2500000000 4771510488401 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5569701359/10000000000 : ℝ)^4507 ≤ (23446425440033/50000000000000 : ℝ)^3483 := by
    have hnat : (5569701359 : ℕ)^4507*50000000000000^3483 ≤ 23446425440033^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5569701359 10000000000 23446425440033 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2630811217/5000000000 : ℝ), (-406858533/2500000000 : ℝ), (5569701359/10000000000 : ℝ)] ![(43564128136933/100000000000000 : ℝ), (4771510488401/50000000000000 : ℝ), (23446425440033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2630811217/5000000000 : ℝ)|^4507 ≤ (43564128136933/100000000000000 : ℝ)^3483
        have hw : |(2630811217/5000000000 : ℝ)|=(2630811217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-406858533/2500000000 : ℝ)|^4507 ≤ (4771510488401/50000000000000 : ℝ)^3483
        have hw : |(-406858533/2500000000 : ℝ)|=(406858533/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5569701359/10000000000 : ℝ)|^4507 ≤ (23446425440033/50000000000000 : ℝ)^3483
        have hw : |(5569701359/10000000000 : ℝ)|=(5569701359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s1_6 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (210464891/400000000 : ℝ)*x 0 + (5569701413/10000000000 : ℝ)*x 1 + (-1627434277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (210464891/400000000 : ℝ)^4507 ≤ (43564126433439/100000000000000 : ℝ)^3483 := by
    have hnat : (210464891 : ℕ)^4507*100000000000000^3483 ≤ 43564126433439^3483*400000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210464891 400000000 43564126433439 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5569701413/10000000000 : ℝ)^4507 ≤ (46892851468371/100000000000000 : ℝ)^3483 := by
    have hnat : (5569701413 : ℕ)^4507*100000000000000^3483 ≤ 46892851468371^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5569701413 10000000000 46892851468371 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1627434277/10000000000 : ℝ)^4507 ≤ (4771511038517/50000000000000 : ℝ)^3483 := by
    have hnat : (1627434277 : ℕ)^4507*50000000000000^3483 ≤ 4771511038517^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1627434277 10000000000 4771511038517 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(210464891/400000000 : ℝ), (5569701413/10000000000 : ℝ), (-1627434277/10000000000 : ℝ)] ![(43564126433439/100000000000000 : ℝ), (46892851468371/100000000000000 : ℝ), (4771511038517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(210464891/400000000 : ℝ)|^4507 ≤ (43564126433439/100000000000000 : ℝ)^3483
        have hw : |(210464891/400000000 : ℝ)|=(210464891/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5569701413/10000000000 : ℝ)|^4507 ≤ (46892851468371/100000000000000 : ℝ)^3483
        have hw : |(5569701413/10000000000 : ℝ)|=(5569701413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1627434277/10000000000 : ℝ)|^4507 ≤ (4771511038517/50000000000000 : ℝ)^3483
        have hw : |(-1627434277/10000000000 : ℝ)|=(1627434277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s1_7 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2126438533/5000000000 : ℝ)*x 0 + (4810558221/10000000000 : ℝ)*x 1 + (3752499541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2126438533/5000000000 : ℝ)^4507 ≤ (33076214077617/100000000000000 : ℝ)^3483 := by
    have hnat : (2126438533 : ℕ)^4507*100000000000000^3483 ≤ 33076214077617^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126438533 5000000000 33076214077617 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4810558221/10000000000 : ℝ)^4507 ≤ (9698423311391/25000000000000 : ℝ)^3483 := by
    have hnat : (4810558221 : ℕ)^4507*25000000000000^3483 ≤ 9698423311391^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4810558221 10000000000 9698423311391 25000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3752499541/10000000000 : ℝ)^4507 ≤ (562601853137/2000000000000 : ℝ)^3483 := by
    have hnat : (3752499541 : ℕ)^4507*2000000000000^3483 ≤ 562601853137^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3752499541 10000000000 562601853137 2000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2126438533/5000000000 : ℝ), (4810558221/10000000000 : ℝ), (3752499541/10000000000 : ℝ)] ![(33076214077617/100000000000000 : ℝ), (9698423311391/25000000000000 : ℝ), (562601853137/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2126438533/5000000000 : ℝ)|^4507 ≤ (33076214077617/100000000000000 : ℝ)^3483
        have hw : |(2126438533/5000000000 : ℝ)|=(2126438533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4810558221/10000000000 : ℝ)|^4507 ≤ (9698423311391/25000000000000 : ℝ)^3483
        have hw : |(4810558221/10000000000 : ℝ)|=(4810558221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3752499541/10000000000 : ℝ)|^4507 ≤ (562601853137/2000000000000 : ℝ)^3483
        have hw : |(3752499541/10000000000 : ℝ)|=(3752499541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1505_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162820231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1023/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2737/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (8261/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18409/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1023/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2737/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1023/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2737/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1023/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2737/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1023/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2737/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1023/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2737/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1023/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2737/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2737/100000 : ℝ) ^ (4505/1024 : ℝ) ≤ (13332904485127/100000000000000000000 : ℝ) := by
    have hpowers : (2737/100000 : ℝ)^4505 ≤ (13332904485127/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2737 : ℕ)^4505*100000000000000000000^1024 ≤ 13332904485127^1024*100000^4505 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2737 100000 13332904485127 100000000000000000000 4505 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2737/100000 : ℝ)) (X := (13332904485127/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1023/4000 : ℝ) ^ (4505/1024 : ℝ) ≤ (124081151122090807/50000000000000000000 : ℝ) := by
    have hpowers : (1023/4000 : ℝ)^4505 ≤ (124081151122090807/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1023 : ℕ)^4505*50000000000000000000^1024 ≤ 124081151122090807^1024*4000^4505 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1023 4000 124081151122090807 50000000000000000000 4505 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1023/4000 : ℝ)) (X := (124081151122090807/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000013332904485127/50000000000000000000 : ℝ) ≤ (10000000606121767/10000000000000000 : ℝ) ^ (4505/1024 : ℝ) := by
    have hpowers : (50000013332904485127/50000000000000000000 : ℝ)^1024 ≤ (10000000606121767/10000000000000000 : ℝ)^4505 := by
      have hnat : (50000013332904485127 : ℕ)^1024*10000000000000000^4505 ≤ 10000000606121767^4505*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000013332904485127 50000000000000000000 10000000606121767 10000000000000000 1024 4505 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000606121767/10000000000000000 : ℝ)) (X := (50000013332904485127/50000000000000000000 : ℝ)) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100248175635148666741/100000000000000000000 : ℝ) ≤ (5002817852826687/5000000000000000 : ℝ) ^ (4505/1024 : ℝ) := by
    have hpowers : (100248175635148666741/100000000000000000000 : ℝ)^1024 ≤ (5002817852826687/5000000000000000 : ℝ)^4505 := by
      have hnat : (100248175635148666741 : ℕ)^1024*5000000000000000^4505 ≤ 5002817852826687^4505*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100248175635148666741 100000000000000000000 5002817852826687 5000000000000000 1024 4505 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002817852826687/5000000000000000 : ℝ)) (X := (100248175635148666741/100000000000000000000 : ℝ)) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25124081151122090807/25000000000000000000 : ℝ) ≤ (10011270805184981/10000000000000000 : ℝ) ^ (4505/1024 : ℝ) := by
    have hpowers : (25124081151122090807/25000000000000000000 : ℝ)^1024 ≤ (10011270805184981/10000000000000000 : ℝ)^4505 := by
      have hnat : (25124081151122090807 : ℕ)^1024*10000000000000000^4505 ≤ 10011270805184981^4505*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25124081151122090807 25000000000000000000 10011270805184981 10000000000000000 1024 4505 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011270805184981/10000000000000000 : ℝ)) (X := (25124081151122090807/25000000000000000000 : ℝ)) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13332904485127/100000000000000000000 : ℝ) ≤ ((57087291826943224507/57095000000000000000 : ℝ)+2*(5635099531607/2283800000000000 : ℝ)*(2737/100000 : ℝ))^(4505/1024 : ℝ) := by
    rw [show (57087291826943224507/57095000000000000000 : ℝ)+2*(5635099531607/2283800000000000 : ℝ)*(2737/100000 : ℝ)=(10000000606121767/10000000000000000 : ℝ) by norm_num, show 1+2*(13332904485127/100000000000000000000 : ℝ)=(50000013332904485127/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(124081151122090807/50000000000000000000 : ℝ)+(13332904485127/100000000000000000000 : ℝ) ≤ ((57087291826943224507/57095000000000000000 : ℝ)+(5635099531607/2283800000000000 : ℝ)*((1023/4000 : ℝ)+(2737/100000 : ℝ)))^(4505/1024 : ℝ) := by
    rw [show (57087291826943224507/57095000000000000000 : ℝ)+(5635099531607/2283800000000000 : ℝ)*((1023/4000 : ℝ)+(2737/100000 : ℝ))=(5002817852826687/5000000000000000 : ℝ) by norm_num, show 1+(124081151122090807/50000000000000000000 : ℝ)+(13332904485127/100000000000000000000 : ℝ)=(100248175635148666741/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(124081151122090807/50000000000000000000 : ℝ) ≤ ((57087291826943224507/57095000000000000000 : ℝ)+2*(5635099531607/2283800000000000 : ℝ)*(1023/4000 : ℝ))^(4505/1024 : ℝ) := by
    rw [show (57087291826943224507/57095000000000000000 : ℝ)+2*(5635099531607/2283800000000000 : ℝ)*(1023/4000 : ℝ)=(10011270805184981/10000000000000000 : ℝ) by norm_num, show 1+2*(124081151122090807/50000000000000000000 : ℝ)=(25124081151122090807/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (57087291826943224507/57095000000000000000 : ℝ)*(X 1 0+X 2 0)+(5635099531607/2283800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4505/1024 : ℝ)) (lo := (2737/100000 : ℝ)) (hi := (1023/4000 : ℝ)) (c := (57087291826943224507/57095000000000000000 : ℝ)) (alpha := (5635099531607/2283800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (57087291826943224507/57095000000000000000 : ℝ)*(X 0 1+X 2 1)+(5635099531607/2283800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4505/1024 : ℝ)) (lo := (2737/100000 : ℝ)) (hi := (1023/4000 : ℝ)) (c := (57087291826943224507/57095000000000000000 : ℝ)) (alpha := (5635099531607/2283800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (57087291826943224507/57095000000000000000 : ℝ)*(X 0 2+X 1 2)+(5635099531607/2283800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4505/1024 : ℝ)) (lo := (2737/100000 : ℝ)) (hi := (1023/4000 : ℝ)) (c := (57087291826943224507/57095000000000000000 : ℝ)) (alpha := (5635099531607/2283800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-57777407/312500000 : ℝ)*X 0 0+(1115041493/2000000000 : ℝ)*X 0 1+(2547685297/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2693951401/5000000000 : ℝ)*X 1 0+(-2101767951/10000000000 : ℝ)*X 1 1+(2547683637/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5387902279/10000000000 : ℝ)*X 2 0+(1273842163/2500000000 : ℝ)*X 2 1+(-2101766853/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4252166003/10000000000 : ℝ)*X 0 0+(1870036279/5000000000 : ℝ)*X 0 1+(3014241/6250000 : ℝ)*X 0 2+(4252166003/10000000000 : ℝ)*X 1 0+(1870036279/5000000000 : ℝ)*X 1 1+(3014241/6250000 : ℝ)*X 1 2+(4252166003/10000000000 : ℝ)*X 2 0+(1870036279/5000000000 : ℝ)*X 2 1+(3014241/6250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1849193081/10000000000 : ℝ)*X 0 0+(2550394107/5000000000 : ℝ)*X 0 1+(696212651/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2630811217/5000000000 : ℝ)*X 1 0+(-406858533/2500000000 : ℝ)*X 1 1+(5569701359/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((210464891/400000000 : ℝ)*X 2 0+(5569701413/10000000000 : ℝ)*X 2 1+(-1627434277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2126438533/5000000000 : ℝ)*X 0 0+(4810558221/10000000000 : ℝ)*X 0 1+(3752499541/10000000000 : ℝ)*X 0 2+(2126438533/5000000000 : ℝ)*X 1 0+(4810558221/10000000000 : ℝ)*X 1 1+(3752499541/10000000000 : ℝ)*X 1 2+(2126438533/5000000000 : ℝ)*X 2 0+(4810558221/10000000000 : ℝ)*X 2 1+(3752499541/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24035066332793807975320651479/2854750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (91455111/25000000000000 : ℝ)*(base1) + (311897897/20000000000000 : ℝ)*(base19) + (85862707/6250000000000 : ℝ)*(base23) + (4249639/20000000000000 : ℝ)*(lower2) + (42898213/20000000000000 : ℝ)*(upper5) + (375956145516167/25000000000000 : ℝ)*(major0) + (375956145516167/25000000000000 : ℝ)*(major1) + (1503824582064669/100000000000000 : ℝ)*(major2) + (416807770445249/20000000000000 : ℝ)*(sp0) + (1042017267807903/50000000000000 : ℝ)*(sp1) + (260504639075311/12500000000000 : ℝ)*(sp2) + (461804257635471/50000000000000 : ℝ)*(sp3) + (2391300509/100000000000000 : ℝ)*(sp5) + (1515987997/100000000000000 : ℝ)*(sp7) + (923610397079383/100000000000000 : ℝ)*(f.failure) + (10420192432029/500000000000 : ℝ)*(f.sum) + (31025831546319/228380000000000000000000000000 : ℝ)*base65 + (15413868500946876581/1427375000000000000000000000000000 : ℝ)*base68 + (31994562662580043183/5709500000000000000000000000000000 : ℝ)*base69 + (8608953891085876581/1427375000000000000000000000000000 : ℝ)*base72 + (802746049143461/228380000000000000000000000000 : ℝ)*base74 + (89796484148152543183/5709500000000000000000000000000000 : ℝ)*base75 + (8905900788339170331/1427375000000000000000000000000000 : ℝ)*base78 + (966456512084454669/1427375000000000000000000000000000 : ℝ)*base79 + (52717526280003/57095000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (65397473/10000000000000000000000 : ℝ)*base89 + (65397473/10000000000000000000000 : ℝ)*base91 + (34602527/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5619698028265479990381173577/1427375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (781809133/100000000000000 : ℝ)*(base19) + (387277429/50000000000000 : ℝ)*(base23) + (62387017/50000000000000 : ℝ)*(upper3) + (23710709/100000000000000 : ℝ)*(lower4) + (27517519/100000000000000 : ℝ)*(upper5) + (1538858866130163/100000000000000 : ℝ)*(major0) + (1538858866130163/100000000000000 : ℝ)*(major1) + (1538858866130163/100000000000000 : ℝ)*(major2) + (5350508801/100000000000000 : ℝ)*(sp1) + (5855793043/100000000000000 : ℝ)*(sp2) + (213259004735411/10000000000000 : ℝ)*(sp4) + (133286494689761/6250000000000 : ℝ)*(sp5) + (213258341700621/10000000000000 : ℝ)*(sp6) + (236281888417503/25000000000000 : ℝ)*(sp7) + (236281888417503/25000000000000 : ℝ)*(f.failure) + (213259004735411/10000000000000 : ℝ)*(f.sum) + (142421571956361/114190000000000000000000000000 : ℝ)*base65 + (44279375341818029641/5709500000000000000000000000000000 : ℝ)*base67 + (23657796504608029641/5709500000000000000000000000000000 : ℝ)*base69 + (23735170472451029641/5709500000000000000000000000000000 : ℝ)*base71 + (253466689488831/114190000000000000000000000000 : ℝ)*base73 + (22544576590617029641/5709500000000000000000000000000000 : ℝ)*base75 + (7579381384878470359/5709500000000000000000000000000000 : ℝ)*base78 + (22604953022971029641/5709500000000000000000000000000000 : ℝ)*base79 + (72038423137771/114190000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (12096807/2500000000000000000000 : ℝ)*base90 + (12096807/2500000000000000000000 : ℝ)*base92 + (12096807/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1505_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162820231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1023/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2737/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8261/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18409/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1505_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1505_s2_0 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-937106639/5000000000 : ℝ)*x 0 + (5460193011/10000000000 : ℝ)*x 1 + (5193985571/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (937106639/5000000000 : ℝ)^4507 ≤ (2291174740077/20000000000000 : ℝ)^3483 := by
    have hnat : (937106639 : ℕ)^4507*20000000000000^3483 ≤ 2291174740077^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937106639 5000000000 2291174740077 20000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5460193011/10000000000 : ℝ)^4507 ≤ (45703272294279/100000000000000 : ℝ)^3483 := by
    have hnat : (5460193011 : ℕ)^4507*100000000000000^3483 ≤ 45703272294279^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460193011 10000000000 45703272294279 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5193985571/10000000000 : ℝ)^4507 ≤ (21420426990841/50000000000000 : ℝ)^3483 := by
    have hnat : (5193985571 : ℕ)^4507*50000000000000^3483 ≤ 21420426990841^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193985571 10000000000 21420426990841 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-937106639/5000000000 : ℝ), (5460193011/10000000000 : ℝ), (5193985571/10000000000 : ℝ)] ![(2291174740077/20000000000000 : ℝ), (45703272294279/100000000000000 : ℝ), (21420426990841/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-937106639/5000000000 : ℝ)|^4507 ≤ (2291174740077/20000000000000 : ℝ)^3483
        have hw : |(-937106639/5000000000 : ℝ)|=(937106639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5460193011/10000000000 : ℝ)|^4507 ≤ (45703272294279/100000000000000 : ℝ)^3483
        have hw : |(5460193011/10000000000 : ℝ)|=(5460193011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5193985571/10000000000 : ℝ)|^4507 ≤ (21420426990841/50000000000000 : ℝ)^3483
        have hw : |(5193985571/10000000000 : ℝ)|=(5193985571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s2_1 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5358741293/10000000000 : ℝ)*x 0 + (-1005654651/5000000000 : ℝ)*x 1 + (2596993233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358741293/10000000000 : ℝ)^4507 ≤ (5575931373259/12500000000000 : ℝ)^3483 := by
    have hnat : (5358741293 : ℕ)^4507*12500000000000^3483 ≤ 5575931373259^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358741293 10000000000 5575931373259 12500000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005654651/5000000000 : ℝ)^4507 ≤ (6275842731531/50000000000000 : ℝ)^3483 := by
    have hnat : (1005654651 : ℕ)^4507*50000000000000^3483 ≤ 6275842731531^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005654651 5000000000 6275842731531 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2596993233/5000000000 : ℝ)^4507 ≤ (21420431767063/50000000000000 : ℝ)^3483 := by
    have hnat : (2596993233 : ℕ)^4507*50000000000000^3483 ≤ 21420431767063^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2596993233 5000000000 21420431767063 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358741293/10000000000 : ℝ), (-1005654651/5000000000 : ℝ), (2596993233/5000000000 : ℝ)] ![(5575931373259/12500000000000 : ℝ), (6275842731531/50000000000000 : ℝ), (21420431767063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358741293/10000000000 : ℝ)|^4507 ≤ (5575931373259/12500000000000 : ℝ)^3483
        have hw : |(5358741293/10000000000 : ℝ)|=(5358741293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1005654651/5000000000 : ℝ)|^4507 ≤ (6275842731531/50000000000000 : ℝ)^3483
        have hw : |(-1005654651/5000000000 : ℝ)|=(1005654651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2596993233/5000000000 : ℝ)|^4507 ≤ (21420431767063/50000000000000 : ℝ)^3483
        have hw : |(2596993233/5000000000 : ℝ)|=(2596993233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s2_2 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5358742223/10000000000 : ℝ)*x 0 + (5193985839/10000000000 : ℝ)*x 1 + (-2011308891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358742223/10000000000 : ℝ)^4507 ≤ (356859688029/800000000000 : ℝ)^3483 := by
    have hnat : (5358742223 : ℕ)^4507*800000000000^3483 ≤ 356859688029^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358742223 10000000000 356859688029 800000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5193985839/10000000000 : ℝ)^4507 ≤ (42840856842079/100000000000000 : ℝ)^3483 := by
    have hnat : (5193985839 : ℕ)^4507*100000000000000^3483 ≤ 42840856842079^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193985839 10000000000 42840856842079 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2011308891/10000000000 : ℝ)^4507 ≤ (100413457153/800000000000 : ℝ)^3483 := by
    have hnat : (2011308891 : ℕ)^4507*800000000000^3483 ≤ 100413457153^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011308891 10000000000 100413457153 800000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358742223/10000000000 : ℝ), (5193985839/10000000000 : ℝ), (-2011308891/10000000000 : ℝ)] ![(356859688029/800000000000 : ℝ), (42840856842079/100000000000000 : ℝ), (100413457153/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358742223/10000000000 : ℝ)|^4507 ≤ (356859688029/800000000000 : ℝ)^3483
        have hw : |(5358742223/10000000000 : ℝ)|=(5358742223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5193985839/10000000000 : ℝ)|^4507 ≤ (42840856842079/100000000000000 : ℝ)^3483
        have hw : |(5193985839/10000000000 : ℝ)|=(5193985839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2011308891/10000000000 : ℝ)|^4507 ≤ (100413457153/800000000000 : ℝ)^3483
        have hw : |(-2011308891/10000000000 : ℝ)|=(2011308891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s2_3 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4270328731/10000000000 : ℝ)*x 0 + (497375349/1250000000 : ℝ)*x 1 + (4579675259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4270328731/10000000000 : ℝ)^4507 ≤ (33251952027993/100000000000000 : ℝ)^3483 := by
    have hnat : (4270328731 : ℕ)^4507*100000000000000^3483 ≤ 33251952027993^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4270328731 10000000000 33251952027993 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (497375349/1250000000 : ℝ)^4507 ≤ (15173232260827/50000000000000 : ℝ)^3483 := by
    have hnat : (497375349 : ℕ)^4507*50000000000000^3483 ≤ 15173232260827^3483*1250000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497375349 1250000000 15173232260827 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4579675259/10000000000 : ℝ)^4507 ≤ (1456063337093/4000000000000 : ℝ)^3483 := by
    have hnat : (4579675259 : ℕ)^4507*4000000000000^3483 ≤ 1456063337093^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4579675259 10000000000 1456063337093 4000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4270328731/10000000000 : ℝ), (497375349/1250000000 : ℝ), (4579675259/10000000000 : ℝ)] ![(33251952027993/100000000000000 : ℝ), (15173232260827/50000000000000 : ℝ), (1456063337093/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4270328731/10000000000 : ℝ)|^4507 ≤ (33251952027993/100000000000000 : ℝ)^3483
        have hw : |(4270328731/10000000000 : ℝ)|=(4270328731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(497375349/1250000000 : ℝ)|^4507 ≤ (15173232260827/50000000000000 : ℝ)^3483
        have hw : |(497375349/1250000000 : ℝ)|=(497375349/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4579675259/10000000000 : ℝ)|^4507 ≤ (1456063337093/4000000000000 : ℝ)^3483
        have hw : |(4579675259/10000000000 : ℝ)|=(4579675259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s2_4 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-374853403/2000000000 : ℝ)*x 0 + (324728901/625000000 : ℝ)*x 1 + (5458501231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (374853403/2000000000 : ℝ)^4507 ≤ (143203734117/1250000000000 : ℝ)^3483 := by
    have hnat : (374853403 : ℕ)^4507*1250000000000^3483 ≤ 143203734117^3483*2000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374853403 2000000000 143203734117 1250000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (324728901/625000000 : ℝ)^4507 ≤ (5357344000231/12500000000000 : ℝ)^3483 := by
    have hnat : (324728901 : ℕ)^4507*12500000000000^3483 ≤ 5357344000231^3483*625000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324728901 625000000 5357344000231 12500000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5458501231/10000000000 : ℝ)^4507 ≤ (5710618656999/12500000000000 : ℝ)^3483 := by
    have hnat : (5458501231 : ℕ)^4507*12500000000000^3483 ≤ 5710618656999^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458501231 10000000000 5710618656999 12500000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-374853403/2000000000 : ℝ), (324728901/625000000 : ℝ), (5458501231/10000000000 : ℝ)] ![(143203734117/1250000000000 : ℝ), (5357344000231/12500000000000 : ℝ), (5710618656999/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-374853403/2000000000 : ℝ)|^4507 ≤ (143203734117/1250000000000 : ℝ)^3483
        have hw : |(-374853403/2000000000 : ℝ)|=(374853403/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(324728901/625000000 : ℝ)|^4507 ≤ (5357344000231/12500000000000 : ℝ)^3483
        have hw : |(324728901/625000000 : ℝ)|=(324728901/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5458501231/10000000000 : ℝ)|^4507 ≤ (5710618656999/12500000000000 : ℝ)^3483
        have hw : |(5458501231/10000000000 : ℝ)|=(5458501231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s2_5 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644456917/5000000000 : ℝ)*x 0 + (-1746794599/10000000000 : ℝ)*x 1 + (341156319/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644456917/5000000000 : ℝ)^4507 ≤ (43856745337959/100000000000000 : ℝ)^3483 := by
    have hnat : (2644456917 : ℕ)^4507*100000000000000^3483 ≤ 43856745337959^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644456917 5000000000 43856745337959 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1746794599/10000000000 : ℝ)^4507 ≤ (5229153384353/50000000000000 : ℝ)^3483 := by
    have hnat : (1746794599 : ℕ)^4507*50000000000000^3483 ≤ 5229153384353^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1746794599 10000000000 5229153384353 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (341156319/625000000 : ℝ)^4507 ≤ (9136989576113/20000000000000 : ℝ)^3483 := by
    have hnat : (341156319 : ℕ)^4507*20000000000000^3483 ≤ 9136989576113^3483*625000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341156319 625000000 9136989576113 20000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644456917/5000000000 : ℝ), (-1746794599/10000000000 : ℝ), (341156319/625000000 : ℝ)] ![(43856745337959/100000000000000 : ℝ), (5229153384353/50000000000000 : ℝ), (9136989576113/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644456917/5000000000 : ℝ)|^4507 ≤ (43856745337959/100000000000000 : ℝ)^3483
        have hw : |(2644456917/5000000000 : ℝ)|=(2644456917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1746794599/10000000000 : ℝ)|^4507 ≤ (5229153384353/50000000000000 : ℝ)^3483
        have hw : |(-1746794599/10000000000 : ℝ)|=(1746794599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(341156319/625000000 : ℝ)|^4507 ≤ (9136989576113/20000000000000 : ℝ)^3483
        have hw : |(341156319/625000000 : ℝ)|=(341156319/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s2_6 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (26444573/50000000 : ℝ)*x 0 + (545850067/1000000000 : ℝ)*x 1 + (-54587317/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26444573/50000000 : ℝ)^4507 ≤ (2192837677861/5000000000000 : ℝ)^3483 := by
    have hnat : (26444573 : ℕ)^4507*5000000000000^3483 ≤ 2192837677861^3483*50000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26444573 50000000 2192837677861 5000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545850067/1000000000 : ℝ)^4507 ≤ (45684943180287/100000000000000 : ℝ)^3483 := by
    have hnat : (545850067 : ℕ)^4507*100000000000000^3483 ≤ 45684943180287^3483*1000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545850067 1000000000 45684943180287 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54587317/312500000 : ℝ)^4507 ≤ (10458303243659/100000000000000 : ℝ)^3483 := by
    have hnat : (54587317 : ℕ)^4507*100000000000000^3483 ≤ 10458303243659^3483*312500000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54587317 312500000 10458303243659 100000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26444573/50000000 : ℝ), (545850067/1000000000 : ℝ), (-54587317/312500000 : ℝ)] ![(2192837677861/5000000000000 : ℝ), (45684943180287/100000000000000 : ℝ), (10458303243659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26444573/50000000 : ℝ)|^4507 ≤ (2192837677861/5000000000000 : ℝ)^3483
        have hw : |(26444573/50000000 : ℝ)|=(26444573/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(545850067/1000000000 : ℝ)|^4507 ≤ (45684943180287/100000000000000 : ℝ)^3483
        have hw : |(545850067/1000000000 : ℝ)|=(545850067/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-54587317/312500000 : ℝ)|^4507 ≤ (10458303243659/100000000000000 : ℝ)^3483
        have hw : |(-54587317/312500000 : ℝ)|=(54587317/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1505_s2_7 (p : ℝ) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4270450953/10000000000 : ℝ)*x 0 + (2287945527/5000000000 : ℝ)*x 1 + (995705223/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4270450953/10000000000 : ℝ)^4507 ≤ (16626591773521/50000000000000 : ℝ)^3483 := by
    have hnat : (4270450953 : ℕ)^4507*50000000000000^3483 ≤ 16626591773521^3483*10000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4270450953 10000000000 16626591773521 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2287945527/5000000000 : ℝ)^4507 ≤ (18181333114621/50000000000000 : ℝ)^3483 := by
    have hnat : (2287945527 : ℕ)^4507*50000000000000^3483 ≤ 18181333114621^3483*5000000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2287945527 5000000000 18181333114621 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (995705223/2500000000 : ℝ)^4507 ≤ (15192075106263/50000000000000 : ℝ)^3483 := by
    have hnat : (995705223 : ℕ)^4507*50000000000000^3483 ≤ 15192075106263^3483*2500000000^4507 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      995705223 2500000000 15192075106263 50000000000000 4507 3483 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4507/1024 : ℝ)) 4507 3483 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4270450953/10000000000 : ℝ), (2287945527/5000000000 : ℝ), (995705223/2500000000 : ℝ)] ![(16626591773521/50000000000000 : ℝ), (18181333114621/50000000000000 : ℝ), (15192075106263/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4270450953/10000000000 : ℝ)|^4507 ≤ (16626591773521/50000000000000 : ℝ)^3483
        have hw : |(4270450953/10000000000 : ℝ)|=(4270450953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2287945527/5000000000 : ℝ)|^4507 ≤ (18181333114621/50000000000000 : ℝ)^3483
        have hw : |(2287945527/5000000000 : ℝ)|=(2287945527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(995705223/2500000000 : ℝ)|^4507 ≤ (15192075106263/50000000000000 : ℝ)^3483
        have hw : |(995705223/2500000000 : ℝ)|=(995705223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1505_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162820231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18409/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8261/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10389/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2003/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18409/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8261/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18409/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8261/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18409/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8261/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18409/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8261/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18409/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8261/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18409/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8261/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8261/100000 : ℝ) ^ (4505/1024 : ℝ) ≤ (1720196614942423/100000000000000000000 : ℝ) := by
    have hpowers : (8261/100000 : ℝ)^4505 ≤ (1720196614942423/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8261 : ℕ)^4505*100000000000000000000^1024 ≤ 1720196614942423^1024*100000^4505 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8261 100000 1720196614942423 100000000000000000000 4505 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8261/100000 : ℝ)) (X := (1720196614942423/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18409/100000 : ℝ) ^ (4505/1024 : ℝ) ≤ (58420264153346181/100000000000000000000 : ℝ) := by
    have hpowers : (18409/100000 : ℝ)^4505 ≤ (58420264153346181/100000000000000000000 : ℝ)^1024 := by
      have hnat : (18409 : ℕ)^4505*100000000000000000000^1024 ≤ 58420264153346181^1024*100000^4505 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18409 100000 58420264153346181 100000000000000000000 4505 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18409/100000 : ℝ)) (X := (58420264153346181/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001720196614942423/50000000000000000000 : ℝ) ≤ (10000078200129667/10000000000000000 : ℝ) ^ (4505/1024 : ℝ) := by
    have hpowers : (50001720196614942423/50000000000000000000 : ℝ)^1024 ≤ (10000078200129667/10000000000000000 : ℝ)^4505 := by
      have hnat : (50001720196614942423 : ℕ)^1024*10000000000000000^4505 ≤ 10000078200129667^4505*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001720196614942423 50000000000000000000 10000078200129667 10000000000000000 1024 4505 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000078200129667/10000000000000000 : ℝ)) (X := (50001720196614942423/50000000000000000000 : ℝ)) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25015035115192072151/25000000000000000000 : ℝ) ≤ (2500341673295213/2500000000000000 : ℝ) ^ (4505/1024 : ℝ) := by
    have hpowers : (25015035115192072151/25000000000000000000 : ℝ)^1024 ≤ (2500341673295213/2500000000000000 : ℝ)^4505 := by
      have hnat : (25015035115192072151 : ℕ)^1024*2500000000000000^4505 ≤ 2500341673295213^4505*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015035115192072151 25000000000000000000 2500341673295213 2500000000000000 1024 4505 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500341673295213/2500000000000000 : ℝ)) (X := (25015035115192072151/25000000000000000000 : ℝ)) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50058420264153346181/50000000000000000000 : ℝ) ≤ (10002655186232037/10000000000000000 : ℝ) ^ (4505/1024 : ℝ) := by
    have hpowers : (50058420264153346181/50000000000000000000 : ℝ)^1024 ≤ (10002655186232037/10000000000000000 : ℝ)^4505 := by
      have hnat : (50058420264153346181 : ℕ)^1024*10000000000000000^4505 ≤ 10002655186232037^4505*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50058420264153346181 50000000000000000000 10002655186232037 10000000000000000 1024 4505 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002655186232037/10000000000000000 : ℝ)) (X := (50058420264153346181/50000000000000000000 : ℝ)) (by norm_num) 4505 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1720196614942423/100000000000000000000 : ℝ) ≤ ((50729752546362091073/50740000000000000000 : ℝ)+2*(257698610237/202960000000000 : ℝ)*(8261/100000 : ℝ))^(4505/1024 : ℝ) := by
    rw [show (50729752546362091073/50740000000000000000 : ℝ)+2*(257698610237/202960000000000 : ℝ)*(8261/100000 : ℝ)=(10000078200129667/10000000000000000 : ℝ) by norm_num, show 1+2*(1720196614942423/100000000000000000000 : ℝ)=(50001720196614942423/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(58420264153346181/100000000000000000000 : ℝ)+(1720196614942423/100000000000000000000 : ℝ) ≤ ((50729752546362091073/50740000000000000000 : ℝ)+(257698610237/202960000000000 : ℝ)*((18409/100000 : ℝ)+(8261/100000 : ℝ)))^(4505/1024 : ℝ) := by
    rw [show (50729752546362091073/50740000000000000000 : ℝ)+(257698610237/202960000000000 : ℝ)*((18409/100000 : ℝ)+(8261/100000 : ℝ))=(2500341673295213/2500000000000000 : ℝ) by norm_num, show 1+(58420264153346181/100000000000000000000 : ℝ)+(1720196614942423/100000000000000000000 : ℝ)=(25015035115192072151/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(58420264153346181/100000000000000000000 : ℝ) ≤ ((50729752546362091073/50740000000000000000 : ℝ)+2*(257698610237/202960000000000 : ℝ)*(18409/100000 : ℝ))^(4505/1024 : ℝ) := by
    rw [show (50729752546362091073/50740000000000000000 : ℝ)+2*(257698610237/202960000000000 : ℝ)*(18409/100000 : ℝ)=(10002655186232037/10000000000000000 : ℝ) by norm_num, show 1+2*(58420264153346181/100000000000000000000 : ℝ)=(50058420264153346181/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (50729752546362091073/50740000000000000000 : ℝ)*(X 1 0+X 2 0)+(257698610237/202960000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4505/1024 : ℝ)) (lo := (8261/100000 : ℝ)) (hi := (18409/100000 : ℝ)) (c := (50729752546362091073/50740000000000000000 : ℝ)) (alpha := (257698610237/202960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (50729752546362091073/50740000000000000000 : ℝ)*(X 0 1+X 2 1)+(257698610237/202960000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4505/1024 : ℝ)) (lo := (8261/100000 : ℝ)) (hi := (18409/100000 : ℝ)) (c := (50729752546362091073/50740000000000000000 : ℝ)) (alpha := (257698610237/202960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (50729752546362091073/50740000000000000000 : ℝ)*(X 0 2+X 1 2)+(257698610237/202960000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4505/1024 : ℝ)) (lo := (8261/100000 : ℝ)) (hi := (18409/100000 : ℝ)) (c := (50729752546362091073/50740000000000000000 : ℝ)) (alpha := (257698610237/202960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-937106639/5000000000 : ℝ)*X 0 0+(5460193011/10000000000 : ℝ)*X 0 1+(5193985571/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5358741293/10000000000 : ℝ)*X 1 0+(-1005654651/5000000000 : ℝ)*X 1 1+(2596993233/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5358742223/10000000000 : ℝ)*X 2 0+(5193985839/10000000000 : ℝ)*X 2 1+(-2011308891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4270328731/10000000000 : ℝ)*X 0 0+(497375349/1250000000 : ℝ)*X 0 1+(4579675259/10000000000 : ℝ)*X 0 2+(4270328731/10000000000 : ℝ)*X 1 0+(497375349/1250000000 : ℝ)*X 1 1+(4579675259/10000000000 : ℝ)*X 1 2+(4270328731/10000000000 : ℝ)*X 2 0+(497375349/1250000000 : ℝ)*X 2 1+(4579675259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-374853403/2000000000 : ℝ)*X 0 0+(324728901/625000000 : ℝ)*X 0 1+(5458501231/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644456917/5000000000 : ℝ)*X 1 0+(-1746794599/10000000000 : ℝ)*X 1 1+(341156319/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((26444573/50000000 : ℝ)*X 2 0+(545850067/1000000000 : ℝ)*X 2 1+(-54587317/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4270450953/10000000000 : ℝ)*X 0 0+(2287945527/5000000000 : ℝ)*X 0 1+(995705223/2500000000 : ℝ)*X 0 2+(4270450953/10000000000 : ℝ)*X 1 0+(2287945527/5000000000 : ℝ)*X 1 1+(995705223/2500000000 : ℝ)*X 1 2+(4270450953/10000000000 : ℝ)*X 2 0+(2287945527/5000000000 : ℝ)*X 2 1+(995705223/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1505_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6856720515581651215723757991/634250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2028109357/100000000000000 : ℝ)*(base19) + (23755669/1000000000000 : ℝ)*(base23) + (176037781/100000000000000 : ℝ)*(upper3) + (10197799/6250000000000 : ℝ)*(upper4) + (201860337/50000000000000 : ℝ)*(upper5) + (1355344864141089/50000000000000 : ℝ)*(major0) + (1355344864141089/50000000000000 : ℝ)*(major1) + (2710689728282179/100000000000000 : ℝ)*(major2) + (3756500248870543/100000000000000 : ℝ)*(sp0) + (1878270562511863/50000000000000 : ℝ)*(sp1) + (1878270388783091/50000000000000 : ℝ)*(sp2) + (66592731405513/4000000000000 : ℝ)*(sp3) + (42904262539/100000000000000 : ℝ)*(sp4) + (8828967493/50000000000000 : ℝ)*(sp7) + (1664835943072811/100000000000000 : ℝ)*(f.failure) + (1878271576566541/50000000000000 : ℝ)*(f.sum) + (25908805856563/4059200000000000000000000000 : ℝ)*base66 + (16299291142174726503/2537000000000000000000000000000000 : ℝ)*base68 + (20541904164261388067/5074000000000000000000000000000000 : ℝ)*base69 + (38091303238744726503/2537000000000000000000000000000000 : ℝ)*base72 + (76871309958577/20296000000000000000000000000 : ℝ)*base73 + (45954244715534611933/5074000000000000000000000000000000 : ℝ)*base76 + (24269934975140351503/2537000000000000000000000000000000 : ℝ)*base78 + (12733752058491351503/2537000000000000000000000000000000 : ℝ)*base80 + (748101948757/5074000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (136839341/10000000000000000000000 : ℝ)*base89 + (136839341/10000000000000000000000 : ℝ)*base91 + (36839341/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7343471869516892626298673891/634250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1787427259/100000000000000 : ℝ)*(base19) + (486237817/20000000000000 : ℝ)*(base23) + (233041769/100000000000000 : ℝ)*(upper3) + (43601/2000000000000 : ℝ)*(lower4) + (303584977/100000000000000 : ℝ)*(upper5) + (686344982704689/25000000000000 : ℝ)*(major0) + (686344982704689/25000000000000 : ℝ)*(major1) + (686344982704689/25000000000000 : ℝ)*(major2) + (20051800653/100000000000000 : ℝ)*(sp1) + (13381748091/50000000000000 : ℝ)*(sp2) + (76092354041267/2000000000000 : ℝ)*(sp4) + (1902297931417719/50000000000000 : ℝ)*(sp5) + (3804588507378083/100000000000000 : ℝ)*(sp6) + (843070886817117/50000000000000 : ℝ)*(sp7) + (843070886817117/50000000000000 : ℝ)*(f.failure) + (76092354041267/2000000000000 : ℝ)*(f.sum) + (10275621594531/2537000000000000000000000000 : ℝ)*base66 + (3718845448760608703/1268500000000000000000000000000000 : ℝ)*base68 + (2678173556587608703/1268500000000000000000000000000000 : ℝ)*base70 + (6858563566670108703/1268500000000000000000000000000000 : ℝ)*base72 + (12210450224223/2537000000000000000000000000 : ℝ)*base74 + (4564578356412391297/1268500000000000000000000000000000 : ℝ)*base75 + (11605659402072608703/1268500000000000000000000000000000 : ℝ)*base78 + (16334454085141391297/1268500000000000000000000000000000 : ℝ)*base79 + (426124261937/101480000000000000000000000 : ℝ)*base82 + (44694027/5000000000000000000000 : ℝ)*base89 + (44694027/5000000000000000000000 : ℝ)*base91 + (44694027/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1505_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162820231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18409/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8261/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10389/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2003/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1505_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1505_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162820231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10389/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2003/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1505_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1505_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1505_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4505/1024 : ℝ) ≤ p) (hpb : p ≤ (4507/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (162820231/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10389/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2003/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1505_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
