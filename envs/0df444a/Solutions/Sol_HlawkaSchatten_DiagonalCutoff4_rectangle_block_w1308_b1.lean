-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1308_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:38:40.681244+00:00
-- url     : https://prove2.me/submissions/29c646c7-8a31-478d-a464-e8973a5c485b

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
theorem support_rectangle_w1308_s3_0 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2071566433/10000000000 : ℝ)*x 0 + (2715877417/5000000000 : ℝ)*x 1 + (2613808103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2071566433/10000000000 : ℝ)^1067 ≤ (6301616774963/50000000000000 : ℝ)^811 := by
    have hnat : (2071566433 : ℕ)^1067*50000000000000^811 ≤ 6301616774963^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071566433 10000000000 6301616774963 50000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2715877417/5000000000 : ℝ)^1067 ≤ (8959864686803/20000000000000 : ℝ)^811 := by
    have hnat : (2715877417 : ℕ)^1067*20000000000000^811 ≤ 8959864686803^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715877417 5000000000 8959864686803 20000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2613808103/5000000000 : ℝ)^1067 ≤ (42597443005569/100000000000000 : ℝ)^811 := by
    have hnat : (2613808103 : ℕ)^1067*100000000000000^811 ≤ 42597443005569^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613808103 5000000000 42597443005569 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2071566433/10000000000 : ℝ), (2715877417/5000000000 : ℝ), (2613808103/5000000000 : ℝ)] ![(6301616774963/50000000000000 : ℝ), (8959864686803/20000000000000 : ℝ), (42597443005569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2071566433/10000000000 : ℝ)|^1067 ≤ (6301616774963/50000000000000 : ℝ)^811
        have hw : |(-2071566433/10000000000 : ℝ)|=(2071566433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2715877417/5000000000 : ℝ)|^1067 ≤ (8959864686803/20000000000000 : ℝ)^811
        have hw : |(2715877417/5000000000 : ℝ)|=(2715877417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2613808103/5000000000 : ℝ)|^1067 ≤ (42597443005569/100000000000000 : ℝ)^811
        have hw : |(2613808103/5000000000 : ℝ)|=(2613808103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s3_1 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5353942163/10000000000 : ℝ)*x 0 + (-1087996313/5000000000 : ℝ)*x 1 + (2613808081/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353942163/10000000000 : ℝ)^1067 ≤ (21978441794267/50000000000000 : ℝ)^811 := by
    have hnat : (5353942163 : ℕ)^1067*50000000000000^811 ≤ 21978441794267^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353942163 10000000000 21978441794267 50000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087996313/5000000000 : ℝ)^1067 ≤ (13445673855797/100000000000000 : ℝ)^811 := by
    have hnat : (1087996313 : ℕ)^1067*100000000000000^811 ≤ 13445673855797^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087996313 5000000000 13445673855797 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2613808081/5000000000 : ℝ)^1067 ≤ (21298721266929/50000000000000 : ℝ)^811 := by
    have hnat : (2613808081 : ℕ)^1067*50000000000000^811 ≤ 21298721266929^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613808081 5000000000 21298721266929 50000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353942163/10000000000 : ℝ), (-1087996313/5000000000 : ℝ), (2613808081/5000000000 : ℝ)] ![(21978441794267/50000000000000 : ℝ), (13445673855797/100000000000000 : ℝ), (21298721266929/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353942163/10000000000 : ℝ)|^1067 ≤ (21978441794267/50000000000000 : ℝ)^811
        have hw : |(5353942163/10000000000 : ℝ)|=(5353942163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1087996313/5000000000 : ℝ)|^1067 ≤ (13445673855797/100000000000000 : ℝ)^811
        have hw : |(-1087996313/5000000000 : ℝ)|=(1087996313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2613808081/5000000000 : ℝ)|^1067 ≤ (21298721266929/50000000000000 : ℝ)^811
        have hw : |(2613808081/5000000000 : ℝ)|=(2613808081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s3_2 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2676971039/5000000000 : ℝ)*x 0 + (2613808177/5000000000 : ℝ)*x 1 + (-1087996243/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676971039/5000000000 : ℝ)^1067 ≤ (2197844133519/5000000000000 : ℝ)^811 := by
    have hnat : (2676971039 : ℕ)^1067*5000000000000^811 ≤ 2197844133519^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676971039 5000000000 2197844133519 5000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2613808177/5000000000 : ℝ)^1067 ≤ (21298722296117/50000000000000 : ℝ)^811 := by
    have hnat : (2613808177 : ℕ)^1067*50000000000000^811 ≤ 21298722296117^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613808177 5000000000 21298722296117 50000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1087996243/5000000000 : ℝ)^1067 ≤ (6722836358827/50000000000000 : ℝ)^811 := by
    have hnat : (1087996243 : ℕ)^1067*50000000000000^811 ≤ 6722836358827^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087996243 5000000000 6722836358827 50000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676971039/5000000000 : ℝ), (2613808177/5000000000 : ℝ), (-1087996243/5000000000 : ℝ)] ![(2197844133519/5000000000000 : ℝ), (21298722296117/50000000000000 : ℝ), (6722836358827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676971039/5000000000 : ℝ)|^1067 ≤ (2197844133519/5000000000000 : ℝ)^811
        have hw : |(2676971039/5000000000 : ℝ)|=(2676971039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2613808177/5000000000 : ℝ)|^1067 ≤ (21298722296117/50000000000000 : ℝ)^811
        have hw : |(2613808177/5000000000 : ℝ)|=(2613808177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1087996243/5000000000 : ℝ)|^1067 ≤ (6722836358827/50000000000000 : ℝ)^811
        have hw : |(-1087996243/5000000000 : ℝ)|=(1087996243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s3_3 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4334294719/10000000000 : ℝ)*x 0 + (825621737/2000000000 : ℝ)*x 1 + (4550228213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4334294719/10000000000 : ℝ)^1067 ≤ (33289573375743/100000000000000 : ℝ)^811 := by
    have hnat : (4334294719 : ℕ)^1067*100000000000000^811 ≤ 33289573375743^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4334294719 10000000000 33289573375743 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (825621737/2000000000 : ℝ)^1067 ≤ (6244378808477/20000000000000 : ℝ)^811 := by
    have hnat : (825621737 : ℕ)^1067*20000000000000^811 ≤ 6244378808477^811*2000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825621737 2000000000 6244378808477 20000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4550228213/10000000000 : ℝ)^1067 ≤ (35488532559687/100000000000000 : ℝ)^811 := by
    have hnat : (4550228213 : ℕ)^1067*100000000000000^811 ≤ 35488532559687^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4550228213 10000000000 35488532559687 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4334294719/10000000000 : ℝ), (825621737/2000000000 : ℝ), (4550228213/10000000000 : ℝ)] ![(33289573375743/100000000000000 : ℝ), (6244378808477/20000000000000 : ℝ), (35488532559687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4334294719/10000000000 : ℝ)|^1067 ≤ (33289573375743/100000000000000 : ℝ)^811
        have hw : |(4334294719/10000000000 : ℝ)|=(4334294719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(825621737/2000000000 : ℝ)|^1067 ≤ (6244378808477/20000000000000 : ℝ)^811
        have hw : |(825621737/2000000000 : ℝ)|=(825621737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4550228213/10000000000 : ℝ)|^1067 ≤ (35488532559687/100000000000000 : ℝ)^811
        have hw : |(4550228213/10000000000 : ℝ)|=(4550228213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s3_4 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-517896959/2500000000 : ℝ)*x 0 + (261424277/500000000 : ℝ)*x 1 + (1086176023/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517896959/2500000000 : ℝ)^1067 ≤ (252068097351/2000000000000 : ℝ)^811 := by
    have hnat : (517896959 : ℕ)^1067*2000000000000^811 ≤ 252068097351^811*2500000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517896959 2500000000 252068097351 2000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261424277/500000000 : ℝ)^1067 ≤ (42606763124701/100000000000000 : ℝ)^811 := by
    have hnat : (261424277 : ℕ)^1067*100000000000000^811 ≤ 42606763124701^811*500000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261424277 500000000 42606763124701 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086176023/2000000000 : ℝ)^1067 ≤ (8957966397599/20000000000000 : ℝ)^811 := by
    have hnat : (1086176023 : ℕ)^1067*20000000000000^811 ≤ 8957966397599^811*2000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086176023 2000000000 8957966397599 20000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-517896959/2500000000 : ℝ), (261424277/500000000 : ℝ), (1086176023/2000000000 : ℝ)] ![(252068097351/2000000000000 : ℝ), (42606763124701/100000000000000 : ℝ), (8957966397599/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-517896959/2500000000 : ℝ)|^1067 ≤ (252068097351/2000000000000 : ℝ)^811
        have hw : |(-517896959/2500000000 : ℝ)|=(517896959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(261424277/500000000 : ℝ)|^1067 ≤ (42606763124701/100000000000000 : ℝ)^811
        have hw : |(261424277/500000000 : ℝ)|=(261424277/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086176023/2000000000 : ℝ)|^1067 ≤ (8957966397599/20000000000000 : ℝ)^811
        have hw : |(1086176023/2000000000 : ℝ)|=(1086176023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s3_5 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2650785029/5000000000 : ℝ)*x 0 + (-986364287/5000000000 : ℝ)*x 1 + (67886001/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2650785029/5000000000 : ℝ)^1067 ≤ (43392045089713/100000000000000 : ℝ)^811 := by
    have hnat : (2650785029 : ℕ)^1067*100000000000000^811 ≤ 43392045089713^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650785029 5000000000 43392045089713 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (986364287/5000000000 : ℝ)^1067 ≤ (472724931413/4000000000000 : ℝ)^811 := by
    have hnat : (986364287 : ℕ)^1067*4000000000000^811 ≤ 472724931413^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986364287 5000000000 472724931413 4000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67886001/125000000 : ℝ)^1067 ≤ (1399682237757/3125000000000 : ℝ)^811 := by
    have hnat : (67886001 : ℕ)^1067*3125000000000^811 ≤ 1399682237757^811*125000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67886001 125000000 1399682237757 3125000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2650785029/5000000000 : ℝ), (-986364287/5000000000 : ℝ), (67886001/125000000 : ℝ)] ![(43392045089713/100000000000000 : ℝ), (472724931413/4000000000000 : ℝ), (1399682237757/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2650785029/5000000000 : ℝ)|^1067 ≤ (43392045089713/100000000000000 : ℝ)^811
        have hw : |(2650785029/5000000000 : ℝ)|=(2650785029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-986364287/5000000000 : ℝ)|^1067 ≤ (472724931413/4000000000000 : ℝ)^811
        have hw : |(-986364287/5000000000 : ℝ)|=(986364287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67886001/125000000 : ℝ)|^1067 ≤ (1399682237757/3125000000000 : ℝ)^811
        have hw : |(67886001/125000000 : ℝ)|=(67886001/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s3_6 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (265078509/500000000 : ℝ)*x 0 + (135771999/250000000 : ℝ)*x 1 + (-1972728573/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265078509/500000000 : ℝ)^1067 ≤ (10848011600863/25000000000000 : ℝ)^811 := by
    have hnat : (265078509 : ℕ)^1067*25000000000000^811 ≤ 10848011600863^811*500000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265078509 500000000 10848011600863 25000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135771999/250000000 : ℝ)^1067 ≤ (8957966061231/20000000000000 : ℝ)^811 := by
    have hnat : (135771999 : ℕ)^1067*20000000000000^811 ≤ 8957966061231^811*250000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135771999 250000000 8957966061231 20000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1972728573/10000000000 : ℝ)^1067 ≤ (11818123277443/100000000000000 : ℝ)^811 := by
    have hnat : (1972728573 : ℕ)^1067*100000000000000^811 ≤ 11818123277443^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1972728573 10000000000 11818123277443 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265078509/500000000 : ℝ), (135771999/250000000 : ℝ), (-1972728573/10000000000 : ℝ)] ![(10848011600863/25000000000000 : ℝ), (8957966061231/20000000000000 : ℝ), (11818123277443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265078509/500000000 : ℝ)|^1067 ≤ (10848011600863/25000000000000 : ℝ)^811
        have hw : |(265078509/500000000 : ℝ)|=(265078509/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135771999/250000000 : ℝ)|^1067 ≤ (8957966061231/20000000000000 : ℝ)^811
        have hw : |(135771999/250000000 : ℝ)|=(135771999/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1972728573/10000000000 : ℝ)|^1067 ≤ (11818123277443/100000000000000 : ℝ)^811
        have hw : |(-1972728573/10000000000 : ℝ)|=(1972728573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s3_7 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4334339141/10000000000 : ℝ)*x 0 + (2274215257/5000000000 : ℝ)*x 1 + (4129917137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4334339141/10000000000 : ℝ)^1067 ≤ (16645011128859/50000000000000 : ℝ)^811 := by
    have hnat : (4334339141 : ℕ)^1067*50000000000000^811 ≤ 16645011128859^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4334339141 10000000000 16645011128859 50000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2274215257/5000000000 : ℝ)^1067 ≤ (7094017429869/20000000000000 : ℝ)^811 := by
    have hnat : (2274215257 : ℕ)^1067*20000000000000^811 ≤ 7094017429869^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2274215257 5000000000 7094017429869 20000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4129917137/10000000000 : ℝ)^1067 ≤ (6247978113843/20000000000000 : ℝ)^811 := by
    have hnat : (4129917137 : ℕ)^1067*20000000000000^811 ≤ 6247978113843^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4129917137 10000000000 6247978113843 20000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4334339141/10000000000 : ℝ), (2274215257/5000000000 : ℝ), (4129917137/10000000000 : ℝ)] ![(16645011128859/50000000000000 : ℝ), (7094017429869/20000000000000 : ℝ), (6247978113843/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4334339141/10000000000 : ℝ)|^1067 ≤ (16645011128859/50000000000000 : ℝ)^811
        have hw : |(4334339141/10000000000 : ℝ)|=(4334339141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2274215257/5000000000 : ℝ)|^1067 ≤ (7094017429869/20000000000000 : ℝ)^811
        have hw : |(2274215257/5000000000 : ℝ)|=(2274215257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4129917137/10000000000 : ℝ)|^1067 ≤ (6247978113843/20000000000000 : ℝ)^811
        have hw : |(4129917137/10000000000 : ℝ)|=(4129917137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1308_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153390473/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8123/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (481/5000 : ℝ)*pair X i i ≤ pair X i h) :
    (10727/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7523/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8123/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (481/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8123/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (481/5000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8123/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (481/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8123/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (481/5000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8123/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (481/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8123/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (481/5000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (481/5000 : ℝ) ^ (4267/1024 : ℝ) ≤ (5792932514050281/100000000000000000000 : ℝ) := by
    have hpowers : (481/5000 : ℝ)^4267 ≤ (5792932514050281/100000000000000000000 : ℝ)^1024 := by
      have hnat : (481 : ℕ)^4267*100000000000000000000^1024 ≤ 5792932514050281^1024*5000^4267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        481 5000 5792932514050281 100000000000000000000 4267 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (481/5000 : ℝ)) (X := (5792932514050281/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8123/50000 : ℝ) ^ (4267/1024 : ℝ) ≤ (5142645862840289/10000000000000000000 : ℝ) := by
    have hpowers : (8123/50000 : ℝ)^4267 ≤ (5142645862840289/10000000000000000000 : ℝ)^1024 := by
      have hnat : (8123 : ℕ)^4267*10000000000000000000^1024 ≤ 5142645862840289^1024*50000^4267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8123 50000 5142645862840289 10000000000000000000 4267 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8123/50000 : ℝ)) (X := (5142645862840289/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005792932514050281/50000000000000000000 : ℝ) ≤ (5000139013399189/5000000000000000 : ℝ) ^ (4267/1024 : ℝ) := by
    have hpowers : (50005792932514050281/50000000000000000000 : ℝ)^1024 ≤ (5000139013399189/5000000000000000 : ℝ)^4267 := by
      have hnat : (50005792932514050281 : ℕ)^1024*5000000000000000^4267 ≤ 5000139013399189^4267*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005792932514050281 50000000000000000000 5000139013399189 5000000000000000 1024 4267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000139013399189/5000000000000000 : ℝ)) (X := (50005792932514050281/50000000000000000000 : ℝ)) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100057219391142453171/100000000000000000000 : ℝ) ≤ (10001372859631437/10000000000000000 : ℝ) ^ (4267/1024 : ℝ) := by
    have hpowers : (100057219391142453171/100000000000000000000 : ℝ)^1024 ≤ (10001372859631437/10000000000000000 : ℝ)^4267 := by
      have hnat : (100057219391142453171 : ℕ)^1024*10000000000000000^4267 ≤ 10001372859631437^4267*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100057219391142453171 100000000000000000000 10001372859631437 10000000000000000 1024 4267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001372859631437/10000000000000000 : ℝ)) (X := (100057219391142453171/100000000000000000000 : ℝ)) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5005142645862840289/5000000000000000000 : ℝ) ≤ (625154230779031/625000000000000 : ℝ) ^ (4267/1024 : ℝ) := by
    have hpowers : (5005142645862840289/5000000000000000000 : ℝ)^1024 ≤ (625154230779031/625000000000000 : ℝ)^4267 := by
      have hnat : (5005142645862840289 : ℕ)^1024*625000000000000^4267 ≤ 625154230779031^4267*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5005142645862840289 5000000000000000000 625154230779031 625000000000000 1024 4267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625154230779031/625000000000000 : ℝ)) (X := (5005142645862840289/5000000000000000000 : ℝ)) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5792932514050281/100000000000000000000 : ℝ) ≤ ((16560194405464499367/16565000000000000000 : ℝ)+2*(1094832833059/662600000000000 : ℝ)*(481/5000 : ℝ))^(4267/1024 : ℝ) := by
    rw [show (16560194405464499367/16565000000000000000 : ℝ)+2*(1094832833059/662600000000000 : ℝ)*(481/5000 : ℝ)=(5000139013399189/5000000000000000 : ℝ) by norm_num, show 1+2*(5792932514050281/100000000000000000000 : ℝ)=(50005792932514050281/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5142645862840289/10000000000000000000 : ℝ)+(5792932514050281/100000000000000000000 : ℝ) ≤ ((16560194405464499367/16565000000000000000 : ℝ)+(1094832833059/662600000000000 : ℝ)*((8123/50000 : ℝ)+(481/5000 : ℝ)))^(4267/1024 : ℝ) := by
    rw [show (16560194405464499367/16565000000000000000 : ℝ)+(1094832833059/662600000000000 : ℝ)*((8123/50000 : ℝ)+(481/5000 : ℝ))=(10001372859631437/10000000000000000 : ℝ) by norm_num, show 1+(5142645862840289/10000000000000000000 : ℝ)+(5792932514050281/100000000000000000000 : ℝ)=(100057219391142453171/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5142645862840289/10000000000000000000 : ℝ) ≤ ((16560194405464499367/16565000000000000000 : ℝ)+2*(1094832833059/662600000000000 : ℝ)*(8123/50000 : ℝ))^(4267/1024 : ℝ) := by
    rw [show (16560194405464499367/16565000000000000000 : ℝ)+2*(1094832833059/662600000000000 : ℝ)*(8123/50000 : ℝ)=(625154230779031/625000000000000 : ℝ) by norm_num, show 1+2*(5142645862840289/10000000000000000000 : ℝ)=(5005142645862840289/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (16560194405464499367/16565000000000000000 : ℝ)*(X 1 0+X 2 0)+(1094832833059/662600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4267/1024 : ℝ)) (lo := (481/5000 : ℝ)) (hi := (8123/50000 : ℝ)) (c := (16560194405464499367/16565000000000000000 : ℝ)) (alpha := (1094832833059/662600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (16560194405464499367/16565000000000000000 : ℝ)*(X 0 1+X 2 1)+(1094832833059/662600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4267/1024 : ℝ)) (lo := (481/5000 : ℝ)) (hi := (8123/50000 : ℝ)) (c := (16560194405464499367/16565000000000000000 : ℝ)) (alpha := (1094832833059/662600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (16560194405464499367/16565000000000000000 : ℝ)*(X 0 2+X 1 2)+(1094832833059/662600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4267/1024 : ℝ)) (lo := (481/5000 : ℝ)) (hi := (8123/50000 : ℝ)) (c := (16560194405464499367/16565000000000000000 : ℝ)) (alpha := (1094832833059/662600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2071566433/10000000000 : ℝ)*X 0 0+(2715877417/5000000000 : ℝ)*X 0 1+(2613808103/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353942163/10000000000 : ℝ)*X 1 0+(-1087996313/5000000000 : ℝ)*X 1 1+(2613808081/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676971039/5000000000 : ℝ)*X 2 0+(2613808177/5000000000 : ℝ)*X 2 1+(-1087996243/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4334294719/10000000000 : ℝ)*X 0 0+(825621737/2000000000 : ℝ)*X 0 1+(4550228213/10000000000 : ℝ)*X 0 2+(4334294719/10000000000 : ℝ)*X 1 0+(825621737/2000000000 : ℝ)*X 1 1+(4550228213/10000000000 : ℝ)*X 1 2+(4334294719/10000000000 : ℝ)*X 2 0+(825621737/2000000000 : ℝ)*X 2 1+(4550228213/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-517896959/2500000000 : ℝ)*X 0 0+(261424277/500000000 : ℝ)*X 0 1+(1086176023/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2650785029/5000000000 : ℝ)*X 1 0+(-986364287/5000000000 : ℝ)*X 1 1+(67886001/125000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265078509/500000000 : ℝ)*X 2 0+(135771999/250000000 : ℝ)*X 2 1+(-1972728573/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4334339141/10000000000 : ℝ)*X 0 0+(2274215257/5000000000 : ℝ)*X 0 1+(4129917137/10000000000 : ℝ)*X 0 2+(4334339141/10000000000 : ℝ)*X 1 0+(2274215257/5000000000 : ℝ)*X 1 1+(4129917137/10000000000 : ℝ)*X 1 2+(4334339141/10000000000 : ℝ)*X 2 0+(2274215257/5000000000 : ℝ)*X 2 1+(4129917137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (47179758400734354842444907/5176562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (155559277/10000000000000 : ℝ)*(base19) + (732528901/50000000000000 : ℝ)*(base23) + (6833061/100000000000000 : ℝ)*(lower2) + (110115403/100000000000000 : ℝ)*(upper3) + (114987163/50000000000000 : ℝ)*(upper5) + (45423199554737/1250000000000 : ℝ)*(major0) + (45423199554737/1250000000000 : ℝ)*(major1) + (45423199554737/1250000000000 : ℝ)*(major2) + (4898658332125351/100000000000000 : ℝ)*(sp0) + (1224671705537287/25000000000000 : ℝ)*(sp1) + (1224671728171029/25000000000000 : ℝ)*(sp2) + (1184505517993507/50000000000000 : ℝ)*(sp3) + (3755702071/12500000000000 : ℝ)*(sp4) + (305280633/2500000000000 : ℝ)*(sp7) + (473804649442467/20000000000000 : ℝ)*(f.failure) + (2449344188870959/50000000000000 : ℝ)*(f.sum) + (15202472480749/3313000000000000000000000000 : ℝ)*base65 + (227257809792851479/20706250000000000000000000000000 : ℝ)*base67 + (210463717416526479/20706250000000000000000000000000 : ℝ)*base69 + (129029393436488979/20706250000000000000000000000000 : ℝ)*base71 + (4905068690889/1656500000000000000000000000 : ℝ)*base73 + (246025742056838979/20706250000000000000000000000000 : ℝ)*base75 + (443290097647663979/20706250000000000000000000000000 : ℝ)*base77 + (312629479555788979/20706250000000000000000000000000 : ℝ)*base79 + (7563197880133/1656500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (583109/2000000000000000000000 : ℝ)*base90 + (583109/2000000000000000000000 : ℝ)*base92 + (583109/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (260085421771645304418808143/51765625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (656310169/50000000000000 : ℝ)*(base19) + (22935693/1562500000000 : ℝ)*(base23) + (208807/156250000000 : ℝ)*(upper3) + (8733529/50000000000000 : ℝ)*(lower4) + (14035461/10000000000000 : ℝ)*(upper5) + (458140921122343/12500000000000 : ℝ)*(major0) + (458140921122343/12500000000000 : ℝ)*(major1) + (458140921122343/12500000000000 : ℝ)*(major2) + (552019441/2500000000000 : ℝ)*(sp1) + (2869158999/12500000000000 : ℝ)*(sp2) + (39526756208837/800000000000 : ℝ)*(sp4) + (617602641588331/12500000000000 : ℝ)*(sp5) + (4940820104948281/100000000000000 : ℝ)*(sp6) + (1194705022188289/50000000000000 : ℝ)*(sp7) + (1194705022188289/50000000000000 : ℝ)*(f.failure) + (39526756208837/800000000000 : ℝ)*(f.sum) + (36687699206039/8282500000000000000000000000 : ℝ)*base65 + (1228951752584518119/207062500000000000000000000000000 : ℝ)*base68 + (454936695009330619/207062500000000000000000000000000 : ℝ)*base70 + (548398773305143119/207062500000000000000000000000000 : ℝ)*base72 + (580245129743/258828125000000000000000000 : ℝ)*base74 + (1526890487377143119/207062500000000000000000000000000 : ℝ)*base76 + (573557155490106881/207062500000000000000000000000000 : ℝ)*base77 + (187237589894768119/207062500000000000000000000000000 : ℝ)*base80 + (68642213658483/16565000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (55229303/5000000000000000000000 : ℝ)*base90 + (55229303/5000000000000000000000 : ℝ)*base92 + (55229303/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1308_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153390473/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8123/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (481/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10727/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7523/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1308_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1308_s4_0 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1036664251/5000000000 : ℝ)*x 0 + (5417717727/10000000000 : ℝ)*x 1 + (5240497489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036664251/5000000000 : ℝ)^1067 ≤ (630866983999/5000000000000 : ℝ)^811 := by
    have hnat : (1036664251 : ℕ)^1067*5000000000000^811 ≤ 630866983999^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036664251 5000000000 630866983999 5000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5417717727/10000000000 : ℝ)^1067 ≤ (357176537293/800000000000 : ℝ)^811 := by
    have hnat : (5417717727 : ℕ)^1067*800000000000^811 ≤ 357176537293^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5417717727 10000000000 357176537293 800000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240497489/10000000000 : ℝ)^1067 ≤ (21367796567139/50000000000000 : ℝ)^811 := by
    have hnat : (5240497489 : ℕ)^1067*50000000000000^811 ≤ 21367796567139^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240497489 10000000000 21367796567139 50000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1036664251/5000000000 : ℝ), (5417717727/10000000000 : ℝ), (5240497489/10000000000 : ℝ)] ![(630866983999/5000000000000 : ℝ), (357176537293/800000000000 : ℝ), (21367796567139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1036664251/5000000000 : ℝ)|^1067 ≤ (630866983999/5000000000000 : ℝ)^811
        have hw : |(-1036664251/5000000000 : ℝ)|=(1036664251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5417717727/10000000000 : ℝ)|^1067 ≤ (357176537293/800000000000 : ℝ)^811
        have hw : |(5417717727/10000000000 : ℝ)|=(5417717727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240497489/10000000000 : ℝ)|^1067 ≤ (21367796567139/50000000000000 : ℝ)^811
        have hw : |(5240497489/10000000000 : ℝ)|=(5240497489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s4_1 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5350383889/10000000000 : ℝ)*x 0 + (-1081857657/5000000000 : ℝ)*x 1 + (104809953/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350383889/10000000000 : ℝ)^1067 ≤ (8783690359803/20000000000000 : ℝ)^811 := by
    have hnat : (5350383889 : ℕ)^1067*20000000000000^811 ≤ 8783690359803^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350383889 10000000000 8783690359803 20000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081857657/5000000000 : ℝ)^1067 ≤ (13345953320929/100000000000000 : ℝ)^811 := by
    have hnat : (1081857657 : ℕ)^1067*100000000000000^811 ≤ 13345953320929^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081857657 5000000000 13345953320929 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104809953/200000000 : ℝ)^1067 ≤ (42735594861653/100000000000000 : ℝ)^811 := by
    have hnat : (104809953 : ℕ)^1067*100000000000000^811 ≤ 42735594861653^811*200000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104809953 200000000 42735594861653 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350383889/10000000000 : ℝ), (-1081857657/5000000000 : ℝ), (104809953/200000000 : ℝ)] ![(8783690359803/20000000000000 : ℝ), (13345953320929/100000000000000 : ℝ), (42735594861653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350383889/10000000000 : ℝ)|^1067 ≤ (8783690359803/20000000000000 : ℝ)^811
        have hw : |(5350383889/10000000000 : ℝ)|=(5350383889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1081857657/5000000000 : ℝ)|^1067 ≤ (13345953320929/100000000000000 : ℝ)^811
        have hw : |(-1081857657/5000000000 : ℝ)|=(1081857657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104809953/200000000 : ℝ)|^1067 ≤ (42735594861653/100000000000000 : ℝ)^811
        have hw : |(104809953/200000000 : ℝ)|=(104809953/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s4_2 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1070076813/2000000000 : ℝ)*x 0 + (2620248791/5000000000 : ℝ)*x 1 + (-2163715169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070076813/2000000000 : ℝ)^1067 ≤ (5489806712467/12500000000000 : ℝ)^811 := by
    have hnat : (1070076813 : ℕ)^1067*12500000000000^811 ≤ 5489806712467^811*2000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070076813 2000000000 5489806712467 12500000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620248791/5000000000 : ℝ)^1067 ≤ (42735594132079/100000000000000 : ℝ)^811 := by
    have hnat : (2620248791 : ℕ)^1067*100000000000000^811 ≤ 42735594132079^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620248791 5000000000 42735594132079 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2163715169/10000000000 : ℝ)^1067 ≤ (6672976072121/50000000000000 : ℝ)^811 := by
    have hnat : (2163715169 : ℕ)^1067*50000000000000^811 ≤ 6672976072121^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163715169 10000000000 6672976072121 50000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070076813/2000000000 : ℝ), (2620248791/5000000000 : ℝ), (-2163715169/10000000000 : ℝ)] ![(5489806712467/12500000000000 : ℝ), (42735594132079/100000000000000 : ℝ), (6672976072121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070076813/2000000000 : ℝ)|^1067 ≤ (5489806712467/12500000000000 : ℝ)^811
        have hw : |(1070076813/2000000000 : ℝ)|=(1070076813/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620248791/5000000000 : ℝ)|^1067 ≤ (42735594132079/100000000000000 : ℝ)^811
        have hw : |(2620248791/5000000000 : ℝ)|=(2620248791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2163715169/10000000000 : ℝ)|^1067 ≤ (6672976072121/50000000000000 : ℝ)^811
        have hw : |(-2163715169/10000000000 : ℝ)|=(2163715169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s4_3 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1083840261/2500000000 : ℝ)*x 0 + (831161217/2000000000 : ℝ)*x 1 + (36178107/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083840261/2500000000 : ℝ)^1067 ≤ (133201395739/400000000000 : ℝ)^811 := by
    have hnat : (1083840261 : ℕ)^1067*400000000000^811 ≤ 133201395739^811*2500000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083840261 2500000000 133201395739 400000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (831161217/2000000000 : ℝ)^1067 ≤ (31497792736057/100000000000000 : ℝ)^811 := by
    have hnat : (831161217 : ℕ)^1067*100000000000000^811 ≤ 31497792736057^811*2000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831161217 2000000000 31497792736057 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36178107/80000000 : ℝ)^1067 ≤ (440023228941/1250000000000 : ℝ)^811 := by
    have hnat : (36178107 : ℕ)^1067*1250000000000^811 ≤ 440023228941^811*80000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36178107 80000000 440023228941 1250000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083840261/2500000000 : ℝ), (831161217/2000000000 : ℝ), (36178107/80000000 : ℝ)] ![(133201395739/400000000000 : ℝ), (31497792736057/100000000000000 : ℝ), (440023228941/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083840261/2500000000 : ℝ)|^1067 ≤ (133201395739/400000000000 : ℝ)^811
        have hw : |(1083840261/2500000000 : ℝ)|=(1083840261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(831161217/2000000000 : ℝ)|^1067 ≤ (31497792736057/100000000000000 : ℝ)^811
        have hw : |(831161217/2000000000 : ℝ)|=(831161217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(36178107/80000000 : ℝ)|^1067 ≤ (440023228941/1250000000000 : ℝ)^811
        have hw : |(36178107/80000000 : ℝ)|=(36178107/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s4_4 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-414668473/2000000000 : ℝ)*x 0 + (2620576751/5000000000 : ℝ)*x 1 + (5290096/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (414668473/2000000000 : ℝ)^1067 ≤ (1577181334293/12500000000000 : ℝ)^811 := by
    have hnat : (414668473 : ℕ)^1067*12500000000000^811 ≤ 1577181334293^811*2000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414668473 2000000000 1577181334293 12500000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620576751/5000000000 : ℝ)^1067 ≤ (10685657915437/25000000000000 : ℝ)^811 := by
    have hnat : (2620576751 : ℕ)^1067*25000000000000^811 ≤ 10685657915437^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620576751 5000000000 10685657915437 25000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5290096/9765625 : ℝ)^1067 ≤ (8927983531653/20000000000000 : ℝ)^811 := by
    have hnat : (5290096 : ℕ)^1067*20000000000000^811 ≤ 8927983531653^811*9765625^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290096 9765625 8927983531653 20000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-414668473/2000000000 : ℝ), (2620576751/5000000000 : ℝ), (5290096/9765625 : ℝ)] ![(1577181334293/12500000000000 : ℝ), (10685657915437/25000000000000 : ℝ), (8927983531653/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-414668473/2000000000 : ℝ)|^1067 ≤ (1577181334293/12500000000000 : ℝ)^811
        have hw : |(-414668473/2000000000 : ℝ)|=(414668473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620576751/5000000000 : ℝ)|^1067 ≤ (10685657915437/25000000000000 : ℝ)^811
        have hw : |(2620576751/5000000000 : ℝ)|=(2620576751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5290096/9765625 : ℝ)|^1067 ≤ (8927983531653/20000000000000 : ℝ)^811
        have hw : |(5290096/9765625 : ℝ)|=(5290096/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s4_5 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5304920547/10000000000 : ℝ)*x 0 + (-99357719/500000000 : ℝ)*x 1 + (169283069/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304920547/10000000000 : ℝ)^1067 ≤ (5428515990943/12500000000000 : ℝ)^811 := by
    have hnat : (5304920547 : ℕ)^1067*12500000000000^811 ≤ 5428515990943^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304920547 10000000000 5428515990943 12500000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (99357719/500000000 : ℝ)^1067 ≤ (477278217559/4000000000000 : ℝ)^811 := by
    have hnat : (99357719 : ℕ)^1067*4000000000000^811 ≤ 477278217559^811*500000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99357719 500000000 477278217559 4000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169283069/312500000 : ℝ)^1067 ≤ (44639916617447/100000000000000 : ℝ)^811 := by
    have hnat : (169283069 : ℕ)^1067*100000000000000^811 ≤ 44639916617447^811*312500000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169283069 312500000 44639916617447 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304920547/10000000000 : ℝ), (-99357719/500000000 : ℝ), (169283069/312500000 : ℝ)] ![(5428515990943/12500000000000 : ℝ), (477278217559/4000000000000 : ℝ), (44639916617447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304920547/10000000000 : ℝ)|^1067 ≤ (5428515990943/12500000000000 : ℝ)^811
        have hw : |(5304920547/10000000000 : ℝ)|=(5304920547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-99357719/500000000 : ℝ)|^1067 ≤ (477278217559/4000000000000 : ℝ)^811
        have hw : |(-99357719/500000000 : ℝ)|=(99357719/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169283069/312500000 : ℝ)|^1067 ≤ (44639916617447/100000000000000 : ℝ)^811
        have hw : |(169283069/312500000 : ℝ)|=(169283069/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s4_6 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (663115037/1250000000 : ℝ)*x 0 + (1354264623/2500000000 : ℝ)*x 1 + (-496788583/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663115037/1250000000 : ℝ)^1067 ≤ (43428125224149/100000000000000 : ℝ)^811 := by
    have hnat : (663115037 : ℕ)^1067*100000000000000^811 ≤ 43428125224149^811*1250000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663115037 1250000000 43428125224149 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354264623/2500000000 : ℝ)^1067 ≤ (44639919696533/100000000000000 : ℝ)^811 := by
    have hnat : (1354264623 : ℕ)^1067*100000000000000^811 ≤ 44639919696533^811*2500000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354264623 2500000000 44639919696533 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (496788583/2500000000 : ℝ)^1067 ≤ (11931955059779/100000000000000 : ℝ)^811 := by
    have hnat : (496788583 : ℕ)^1067*100000000000000^811 ≤ 11931955059779^811*2500000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      496788583 2500000000 11931955059779 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663115037/1250000000 : ℝ), (1354264623/2500000000 : ℝ), (-496788583/2500000000 : ℝ)] ![(43428125224149/100000000000000 : ℝ), (44639919696533/100000000000000 : ℝ), (11931955059779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663115037/1250000000 : ℝ)|^1067 ≤ (43428125224149/100000000000000 : ℝ)^811
        have hw : |(663115037/1250000000 : ℝ)|=(663115037/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354264623/2500000000 : ℝ)|^1067 ≤ (44639919696533/100000000000000 : ℝ)^811
        have hw : |(1354264623/2500000000 : ℝ)|=(1354264623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-496788583/2500000000 : ℝ)|^1067 ≤ (11931955059779/100000000000000 : ℝ)^811
        have hw : |(-496788583/2500000000 : ℝ)|=(496788583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s4_7 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1083847421/2500000000 : ℝ)*x 0 + (113022687/250000000 : ℝ)*x 1 + (2078584737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1083847421/2500000000 : ℝ)^1067 ≤ (33300638362751/100000000000000 : ℝ)^811 := by
    have hnat : (1083847421 : ℕ)^1067*100000000000000^811 ≤ 33300638362751^811*2500000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083847421 2500000000 33300638362751 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (113022687/250000000 : ℝ)^1067 ≤ (35187972902023/100000000000000 : ℝ)^811 := by
    have hnat : (113022687 : ℕ)^1067*100000000000000^811 ≤ 35187972902023^811*250000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113022687 250000000 35187972902023 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2078584737/5000000000 : ℝ)^1067 ≤ (31511388721229/100000000000000 : ℝ)^811 := by
    have hnat : (2078584737 : ℕ)^1067*100000000000000^811 ≤ 31511388721229^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078584737 5000000000 31511388721229 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1083847421/2500000000 : ℝ), (113022687/250000000 : ℝ), (2078584737/5000000000 : ℝ)] ![(33300638362751/100000000000000 : ℝ), (35187972902023/100000000000000 : ℝ), (31511388721229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1083847421/2500000000 : ℝ)|^1067 ≤ (33300638362751/100000000000000 : ℝ)^811
        have hw : |(1083847421/2500000000 : ℝ)|=(1083847421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(113022687/250000000 : ℝ)|^1067 ≤ (35187972902023/100000000000000 : ℝ)^811
        have hw : |(113022687/250000000 : ℝ)|=(113022687/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2078584737/5000000000 : ℝ)|^1067 ≤ (31511388721229/100000000000000 : ℝ)^811
        have hw : |(2078584737/5000000000 : ℝ)|=(2078584737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1308_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153390473/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7523/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10727/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5501/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14753/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7523/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10727/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7523/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10727/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7523/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10727/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7523/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10727/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7523/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10727/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7523/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10727/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10727/100000 : ℝ) ^ (4267/1024 : ℝ) ≤ (9120330358999309/100000000000000000000 : ℝ) := by
    have hpowers : (10727/100000 : ℝ)^4267 ≤ (9120330358999309/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10727 : ℕ)^4267*100000000000000000000^1024 ≤ 9120330358999309^1024*100000^4267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10727 100000 9120330358999309 100000000000000000000 4267 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10727/100000 : ℝ)) (X := (9120330358999309/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7523/50000 : ℝ) ^ (4267/1024 : ℝ) ≤ (18676262836996523/50000000000000000000 : ℝ) := by
    have hpowers : (7523/50000 : ℝ)^4267 ≤ (18676262836996523/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7523 : ℕ)^4267*50000000000000000000^1024 ≤ 18676262836996523^1024*50000^4267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7523 50000 18676262836996523 50000000000000000000 4267 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7523/50000 : ℝ)) (X := (18676262836996523/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009120330358999309/50000000000000000000 : ℝ) ≤ (2000087542263863/2000000000000000 : ℝ) ^ (4267/1024 : ℝ) := by
    have hpowers : (50009120330358999309/50000000000000000000 : ℝ)^1024 ≤ (2000087542263863/2000000000000000 : ℝ)^4267 := by
      have hnat : (50009120330358999309 : ℕ)^1024*2000000000000000^4267 ≤ 2000087542263863^4267*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009120330358999309 50000000000000000000 2000087542263863 2000000000000000 1024 4267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000087542263863/2000000000000000 : ℝ)) (X := (50009120330358999309/50000000000000000000 : ℝ)) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009294571206598471/20000000000000000000 : ℝ) ≤ (10001115064512161/10000000000000000 : ℝ) ^ (4267/1024 : ℝ) := by
    have hpowers : (20009294571206598471/20000000000000000000 : ℝ)^1024 ≤ (10001115064512161/10000000000000000 : ℝ)^4267 := by
      have hnat : (20009294571206598471 : ℕ)^1024*10000000000000000^4267 ≤ 10001115064512161^4267*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009294571206598471 20000000000000000000 10001115064512161 10000000000000000 1024 4267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001115064512161/10000000000000000 : ℝ)) (X := (20009294571206598471/20000000000000000000 : ℝ)) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018676262836996523/25000000000000000000 : ℝ) ≤ (10001792417705007/10000000000000000 : ℝ) ^ (4267/1024 : ℝ) := by
    have hpowers : (25018676262836996523/25000000000000000000 : ℝ)^1024 ≤ (10001792417705007/10000000000000000 : ℝ)^4267 := by
      have hnat : (25018676262836996523 : ℕ)^1024*10000000000000000^4267 ≤ 10001792417705007^4267*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018676262836996523 25000000000000000000 10001792417705007 10000000000000000 1024 4267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001792417705007/10000000000000000 : ℝ)) (X := (25018676262836996523/25000000000000000000 : ℝ)) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9120330358999309/100000000000000000000 : ℝ) ≤ ((43177358539788803401/43190000000000000000 : ℝ)+2*(338676596423/215950000000000 : ℝ)*(10727/100000 : ℝ))^(4267/1024 : ℝ) := by
    rw [show (43177358539788803401/43190000000000000000 : ℝ)+2*(338676596423/215950000000000 : ℝ)*(10727/100000 : ℝ)=(2000087542263863/2000000000000000 : ℝ) by norm_num, show 1+2*(9120330358999309/100000000000000000000 : ℝ)=(50009120330358999309/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18676262836996523/50000000000000000000 : ℝ)+(9120330358999309/100000000000000000000 : ℝ) ≤ ((43177358539788803401/43190000000000000000 : ℝ)+(338676596423/215950000000000 : ℝ)*((7523/50000 : ℝ)+(10727/100000 : ℝ)))^(4267/1024 : ℝ) := by
    rw [show (43177358539788803401/43190000000000000000 : ℝ)+(338676596423/215950000000000 : ℝ)*((7523/50000 : ℝ)+(10727/100000 : ℝ))=(10001115064512161/10000000000000000 : ℝ) by norm_num, show 1+(18676262836996523/50000000000000000000 : ℝ)+(9120330358999309/100000000000000000000 : ℝ)=(20009294571206598471/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18676262836996523/50000000000000000000 : ℝ) ≤ ((43177358539788803401/43190000000000000000 : ℝ)+2*(338676596423/215950000000000 : ℝ)*(7523/50000 : ℝ))^(4267/1024 : ℝ) := by
    rw [show (43177358539788803401/43190000000000000000 : ℝ)+2*(338676596423/215950000000000 : ℝ)*(7523/50000 : ℝ)=(10001792417705007/10000000000000000 : ℝ) by norm_num, show 1+2*(18676262836996523/50000000000000000000 : ℝ)=(25018676262836996523/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43177358539788803401/43190000000000000000 : ℝ)*(X 1 0+X 2 0)+(338676596423/215950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4267/1024 : ℝ)) (lo := (10727/100000 : ℝ)) (hi := (7523/50000 : ℝ)) (c := (43177358539788803401/43190000000000000000 : ℝ)) (alpha := (338676596423/215950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43177358539788803401/43190000000000000000 : ℝ)*(X 0 1+X 2 1)+(338676596423/215950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4267/1024 : ℝ)) (lo := (10727/100000 : ℝ)) (hi := (7523/50000 : ℝ)) (c := (43177358539788803401/43190000000000000000 : ℝ)) (alpha := (338676596423/215950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43177358539788803401/43190000000000000000 : ℝ)*(X 0 2+X 1 2)+(338676596423/215950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4267/1024 : ℝ)) (lo := (10727/100000 : ℝ)) (hi := (7523/50000 : ℝ)) (c := (43177358539788803401/43190000000000000000 : ℝ)) (alpha := (338676596423/215950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1036664251/5000000000 : ℝ)*X 0 0+(5417717727/10000000000 : ℝ)*X 0 1+(5240497489/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350383889/10000000000 : ℝ)*X 1 0+(-1081857657/5000000000 : ℝ)*X 1 1+(104809953/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070076813/2000000000 : ℝ)*X 2 0+(2620248791/5000000000 : ℝ)*X 2 1+(-2163715169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1083840261/2500000000 : ℝ)*X 0 0+(831161217/2000000000 : ℝ)*X 0 1+(36178107/80000000 : ℝ)*X 0 2+(1083840261/2500000000 : ℝ)*X 1 0+(831161217/2000000000 : ℝ)*X 1 1+(36178107/80000000 : ℝ)*X 1 2+(1083840261/2500000000 : ℝ)*X 2 0+(831161217/2000000000 : ℝ)*X 2 1+(36178107/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-414668473/2000000000 : ℝ)*X 0 0+(2620576751/5000000000 : ℝ)*X 0 1+(5290096/9765625 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304920547/10000000000 : ℝ)*X 1 0+(-99357719/500000000 : ℝ)*X 1 1+(169283069/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((663115037/1250000000 : ℝ)*X 2 0+(1354264623/2500000000 : ℝ)*X 2 1+(-496788583/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1083847421/2500000000 : ℝ)*X 0 0+(113022687/250000000 : ℝ)*X 0 1+(2078584737/5000000000 : ℝ)*X 0 2+(1083847421/2500000000 : ℝ)*X 1 0+(113022687/250000000 : ℝ)*X 1 1+(2078584737/5000000000 : ℝ)*X 1 2+(1083847421/2500000000 : ℝ)*X 2 0+(113022687/250000000 : ℝ)*X 2 1+(2078584737/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1503829889861119890046221831/154250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1891398149/100000000000000 : ℝ)*(base19) + (391856801/20000000000000 : ℝ)*(base23) + (12598267/20000000000000 : ℝ)*(lower2) + (200620829/100000000000000 : ℝ)*(upper3) + (6300839/2000000000000 : ℝ)*(upper5) + (4185823586098339/100000000000000 : ℝ)*(major0) + (4185823586098339/100000000000000 : ℝ)*(major1) + (4185823586098339/100000000000000 : ℝ)*(major2) + (564273404376677/10000000000000 : ℝ)*(sp0) + (5642776921039499/100000000000000 : ℝ)*(sp1) + (5642776853153643/100000000000000 : ℝ)*(sp2) + (170553104735057/6250000000000 : ℝ)*(sp3) + (44768670877/100000000000000 : ℝ)*(sp4) + (3671804273/20000000000000 : ℝ)*(sp7) + (2728868034782277/100000000000000 : ℝ)*(f.failure) + (352673675777353/6250000000000 : ℝ)*(f.sum) + (4069460465291/21595000000000000000000000000 : ℝ)*base66 + (7121286547687050939/4319000000000000000000000000000000 : ℝ)*base67 + (3234856500808949061/4319000000000000000000000000000000 : ℝ)*base70 + (69674375785877949061/4319000000000000000000000000000000 : ℝ)*base72 + (12879860177141/5398750000000000000000000000 : ℝ)*base73 + (100344220872436949061/4319000000000000000000000000000000 : ℝ)*base76 + (8870056353573949061/4319000000000000000000000000000000 : ℝ)*base78 + (56193086100370949061/4319000000000000000000000000000000 : ℝ)*base80 + (72651717970709/21595000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (21047021/10000000000000000000000 : ℝ)*base89 + (21047021/10000000000000000000000 : ℝ)*base91 + (21047021/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (965624299512629273156840787/154250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1386836141/100000000000000 : ℝ)*(base19) + (1214485211/100000000000000 : ℝ)*(base23) + (40659153/25000000000000 : ℝ)*(upper3) + (15847353/50000000000000 : ℝ)*(lower4) + (68638597/100000000000000 : ℝ)*(upper5) + (4217059736201697/100000000000000 : ℝ)*(major0) + (4217059736201697/100000000000000 : ℝ)*(major1) + (4217059736201697/100000000000000 : ℝ)*(major2) + (5923851329/25000000000000 : ℝ)*(sp1) + (2799864023/10000000000000 : ℝ)*(sp2) + (5684887415284111/100000000000000 : ℝ)*(sp4) + (5684862333042653/100000000000000 : ℝ)*(sp5) + (5684858202158669/100000000000000 : ℝ)*(sp6) + (1374615924224217/50000000000000 : ℝ)*(sp7) + (1374615924224217/50000000000000 : ℝ)*(f.failure) + (5684887415284111/100000000000000 : ℝ)*(f.sum) + (9797761193681/3085000000000000000000000000 : ℝ)*base65 + (803118222573746929/617000000000000000000000000000000 : ℝ)*base68 + (5220394613520253071/617000000000000000000000000000000 : ℝ)*base69 + (9558960602233253071/617000000000000000000000000000000 : ℝ)*base71 + (2876884446797/1542500000000000000000000000 : ℝ)*base74 + (696892752360253071/617000000000000000000000000000000 : ℝ)*base75 + (3714776177230253071/617000000000000000000000000000000 : ℝ)*base77 + (6262652072964253071/617000000000000000000000000000000 : ℝ)*base79 + (1268427504867/385625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (46315359/5000000000000000000000 : ℝ)*base90 + (46315359/5000000000000000000000 : ℝ)*base92 + (46315359/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1308_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153390473/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7523/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10727/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5501/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1308_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1308_s5_0 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-103682441/500000000 : ℝ)*x 0 + (1353746373/2500000000 : ℝ)*x 1 + (2621509553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103682441/500000000 : ℝ)^1067 ≤ (12619904371737/100000000000000 : ℝ)^811 := by
    have hnat : (103682441 : ℕ)^1067*100000000000000^811 ≤ 12619904371737^811*500000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103682441 500000000 12619904371737 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353746373/2500000000 : ℝ)^1067 ≤ (44617445896451/100000000000000 : ℝ)^811 := by
    have hnat : (1353746373 : ℕ)^1067*100000000000000^811 ≤ 44617445896451^811*2500000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353746373 2500000000 44617445896451 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621509553/5000000000 : ℝ)^1067 ≤ (42762649713337/100000000000000 : ℝ)^811 := by
    have hnat : (2621509553 : ℕ)^1067*100000000000000^811 ≤ 42762649713337^811*5000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621509553 5000000000 42762649713337 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-103682441/500000000 : ℝ), (1353746373/2500000000 : ℝ), (2621509553/5000000000 : ℝ)] ![(12619904371737/100000000000000 : ℝ), (44617445896451/100000000000000 : ℝ), (42762649713337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-103682441/500000000 : ℝ)|^1067 ≤ (12619904371737/100000000000000 : ℝ)^811
        have hw : |(-103682441/500000000 : ℝ)|=(103682441/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353746373/2500000000 : ℝ)|^1067 ≤ (44617445896451/100000000000000 : ℝ)^811
        have hw : |(1353746373/2500000000 : ℝ)|=(1353746373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621509553/5000000000 : ℝ)|^1067 ≤ (42762649713337/100000000000000 : ℝ)^811
        have hw : |(2621509553/5000000000 : ℝ)|=(2621509553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s5_1 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1069937901/2000000000 : ℝ)*x 0 + (-54032627/250000000 : ℝ)*x 1 + (5243019091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069937901/2000000000 : ℝ)^1067 ≤ (43910952918173/100000000000000 : ℝ)^811 := by
    have hnat : (1069937901 : ℕ)^1067*100000000000000^811 ≤ 43910952918173^811*2000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069937901 2000000000 43910952918173 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (54032627/250000000 : ℝ)^1067 ≤ (1332639750791/10000000000000 : ℝ)^811 := by
    have hnat : (54032627 : ℕ)^1067*10000000000000^811 ≤ 1332639750791^811*250000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54032627 250000000 1332639750791 10000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243019091/10000000000 : ℝ)^1067 ≤ (42762649552377/100000000000000 : ℝ)^811 := by
    have hnat : (5243019091 : ℕ)^1067*100000000000000^811 ≤ 42762649552377^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243019091 10000000000 42762649552377 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069937901/2000000000 : ℝ), (-54032627/250000000 : ℝ), (5243019091/10000000000 : ℝ)] ![(43910952918173/100000000000000 : ℝ), (1332639750791/10000000000000 : ℝ), (42762649552377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069937901/2000000000 : ℝ)|^1067 ≤ (43910952918173/100000000000000 : ℝ)^811
        have hw : |(1069937901/2000000000 : ℝ)|=(1069937901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-54032627/250000000 : ℝ)|^1067 ≤ (1332639750791/10000000000000 : ℝ)^811
        have hw : |(-54032627/250000000 : ℝ)|=(54032627/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243019091/10000000000 : ℝ)|^1067 ≤ (42762649552377/100000000000000 : ℝ)^811
        have hw : |(5243019091/10000000000 : ℝ)|=(5243019091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s5_2 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1069937897/2000000000 : ℝ)*x 0 + (1048603821/2000000000 : ℝ)*x 1 + (-2161305089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069937897/2000000000 : ℝ)^1067 ≤ (43910952702191/100000000000000 : ℝ)^811 := by
    have hnat : (1069937897 : ℕ)^1067*100000000000000^811 ≤ 43910952702191^811*2000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069937897 2000000000 43910952702191 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1048603821/2000000000 : ℝ)^1067 ≤ (42762649702607/100000000000000 : ℝ)^811 := by
    have hnat : (1048603821 : ℕ)^1067*100000000000000^811 ≤ 42762649702607^811*2000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048603821 2000000000 42762649702607 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2161305089/10000000000 : ℝ)^1067 ≤ (333159939523/2500000000000 : ℝ)^811 := by
    have hnat : (2161305089 : ℕ)^1067*2500000000000^811 ≤ 333159939523^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2161305089 10000000000 333159939523 2500000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069937897/2000000000 : ℝ), (1048603821/2000000000 : ℝ), (-2161305089/10000000000 : ℝ)] ![(43910952702191/100000000000000 : ℝ), (42762649702607/100000000000000 : ℝ), (333159939523/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069937897/2000000000 : ℝ)|^1067 ≤ (43910952702191/100000000000000 : ℝ)^811
        have hw : |(1069937897/2000000000 : ℝ)|=(1069937897/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1048603821/2000000000 : ℝ)|^1067 ≤ (42762649702607/100000000000000 : ℝ)^811
        have hw : |(1048603821/2000000000 : ℝ)|=(1048603821/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2161305089/10000000000 : ℝ)|^1067 ≤ (333159939523/2500000000000 : ℝ)^811
        have hw : |(-2161305089/10000000000 : ℝ)|=(2161305089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s5_3 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (433555133/1000000000 : ℝ)*x 0 + (260075881/625000000 : ℝ)*x 1 + (4516807827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433555133/1000000000 : ℝ)^1067 ≤ (33302271924299/100000000000000 : ℝ)^811 := by
    have hnat : (433555133 : ℕ)^1067*100000000000000^811 ≤ 33302271924299^811*1000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433555133 1000000000 33302271924299 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (260075881/625000000 : ℝ)^1067 ≤ (788793269337/2500000000000 : ℝ)^811 := by
    have hnat : (260075881 : ℕ)^1067*2500000000000^811 ≤ 788793269337^811*625000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260075881 625000000 788793269337 2500000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4516807827/10000000000 : ℝ)^1067 ≤ (4393249660263/12500000000000 : ℝ)^811 := by
    have hnat : (4516807827 : ℕ)^1067*12500000000000^811 ≤ 4393249660263^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516807827 10000000000 4393249660263 12500000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(433555133/1000000000 : ℝ), (260075881/625000000 : ℝ), (4516807827/10000000000 : ℝ)] ![(33302271924299/100000000000000 : ℝ), (788793269337/2500000000000 : ℝ), (4393249660263/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(433555133/1000000000 : ℝ)|^1067 ≤ (33302271924299/100000000000000 : ℝ)^811
        have hw : |(433555133/1000000000 : ℝ)|=(433555133/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(260075881/625000000 : ℝ)|^1067 ≤ (788793269337/2500000000000 : ℝ)^811
        have hw : |(260075881/625000000 : ℝ)|=(260075881/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4516807827/10000000000 : ℝ)|^1067 ≤ (4393249660263/12500000000000 : ℝ)^811
        have hw : |(4516807827/10000000000 : ℝ)|=(4516807827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s5_4 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-103683103/500000000 : ℝ)*x 0 + (5243636329/10000000000 : ℝ)*x 1 + (5414364723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103683103/500000000 : ℝ)^1067 ≤ (12620010383203/100000000000000 : ℝ)^811 := by
    have hnat : (103683103 : ℕ)^1067*100000000000000^811 ≤ 12620010383203^811*500000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103683103 500000000 12620010383203 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243636329/10000000000 : ℝ)^1067 ≤ (42769273051097/100000000000000 : ℝ)^811 := by
    have hnat : (5243636329 : ℕ)^1067*100000000000000^811 ≤ 42769273051097^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243636329 10000000000 42769273051097 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414364723/10000000000 : ℝ)^1067 ≤ (5576339568269/12500000000000 : ℝ)^811 := by
    have hnat : (5414364723 : ℕ)^1067*12500000000000^811 ≤ 5576339568269^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414364723 10000000000 5576339568269 12500000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-103683103/500000000 : ℝ), (5243636329/10000000000 : ℝ), (5414364723/10000000000 : ℝ)] ![(12620010383203/100000000000000 : ℝ), (42769273051097/100000000000000 : ℝ), (5576339568269/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-103683103/500000000 : ℝ)|^1067 ≤ (12620010383203/100000000000000 : ℝ)^811
        have hw : |(-103683103/500000000 : ℝ)|=(103683103/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243636329/10000000000 : ℝ)|^1067 ≤ (42769273051097/100000000000000 : ℝ)^811
        have hw : |(5243636329/10000000000 : ℝ)|=(5243636329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414364723/10000000000 : ℝ)|^1067 ≤ (5576339568269/12500000000000 : ℝ)^811
        have hw : |(5414364723/10000000000 : ℝ)|=(5414364723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s5_5 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305573819/10000000000 : ℝ)*x 0 + (-1989959331/10000000000 : ℝ)*x 1 + (5414364723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305573819/10000000000 : ℝ)^1067 ≤ (43435164129151/100000000000000 : ℝ)^811 := by
    have hnat : (5305573819 : ℕ)^1067*100000000000000^811 ≤ 43435164129151^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305573819 10000000000 43435164129151 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1989959331/10000000000 : ℝ)^1067 ≤ (2988529826939/25000000000000 : ℝ)^811 := by
    have hnat : (1989959331 : ℕ)^1067*25000000000000^811 ≤ 2988529826939^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989959331 10000000000 2988529826939 25000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414364723/10000000000 : ℝ)^1067 ≤ (5576339568269/12500000000000 : ℝ)^811 := by
    have hnat : (5414364723 : ℕ)^1067*12500000000000^811 ≤ 5576339568269^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414364723 10000000000 5576339568269 12500000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305573819/10000000000 : ℝ), (-1989959331/10000000000 : ℝ), (5414364723/10000000000 : ℝ)] ![(43435164129151/100000000000000 : ℝ), (2988529826939/25000000000000 : ℝ), (5576339568269/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305573819/10000000000 : ℝ)|^1067 ≤ (43435164129151/100000000000000 : ℝ)^811
        have hw : |(5305573819/10000000000 : ℝ)|=(5305573819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1989959331/10000000000 : ℝ)|^1067 ≤ (2988529826939/25000000000000 : ℝ)^811
        have hw : |(-1989959331/10000000000 : ℝ)|=(1989959331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414364723/10000000000 : ℝ)|^1067 ≤ (5576339568269/12500000000000 : ℝ)^811
        have hw : |(5414364723/10000000000 : ℝ)|=(5414364723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s5_6 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305574043/10000000000 : ℝ)*x 0 + (270718211/500000000 : ℝ)*x 1 + (-497489929/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305574043/10000000000 : ℝ)^1067 ≤ (10858791635459/25000000000000 : ℝ)^811 := by
    have hnat : (5305574043 : ℕ)^1067*25000000000000^811 ≤ 10858791635459^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305574043 10000000000 10858791635459 25000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270718211/500000000 : ℝ)^1067 ≤ (44610711093557/100000000000000 : ℝ)^811 := by
    have hnat : (270718211 : ℕ)^1067*100000000000000^811 ≤ 44610711093557^811*500000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270718211 500000000 44610711093557 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (497489929/2500000000 : ℝ)^1067 ≤ (5977061175293/50000000000000 : ℝ)^811 := by
    have hnat : (497489929 : ℕ)^1067*50000000000000^811 ≤ 5977061175293^811*2500000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      497489929 2500000000 5977061175293 50000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305574043/10000000000 : ℝ), (270718211/500000000 : ℝ), (-497489929/2500000000 : ℝ)] ![(10858791635459/25000000000000 : ℝ), (44610711093557/100000000000000 : ℝ), (5977061175293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305574043/10000000000 : ℝ)|^1067 ≤ (10858791635459/25000000000000 : ℝ)^811
        have hw : |(5305574043/10000000000 : ℝ)|=(5305574043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270718211/500000000 : ℝ)|^1067 ≤ (44610711093557/100000000000000 : ℝ)^811
        have hw : |(270718211/500000000 : ℝ)|=(270718211/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-497489929/2500000000 : ℝ)|^1067 ≤ (5977061175293/50000000000000 : ℝ)^811
        have hw : |(-497489929/2500000000 : ℝ)|=(497489929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1308_s5_7 (p : ℝ) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4335577791/10000000000 : ℝ)*x 0 + (4515530659/10000000000 : ℝ)*x 1 + (4162497827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4335577791/10000000000 : ℝ)^1067 ≤ (16651269667803/50000000000000 : ℝ)^811 := by
    have hnat : (4335577791 : ℕ)^1067*50000000000000^811 ≤ 16651269667803^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4335577791 10000000000 16651269667803 50000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4515530659/10000000000 : ℝ)^1067 ≤ (35132923041643/100000000000000 : ℝ)^811 := by
    have hnat : (4515530659 : ℕ)^1067*100000000000000^811 ≤ 35132923041643^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515530659 10000000000 35132923041643 100000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4162497827/10000000000 : ℝ)^1067 ≤ (7891134402491/25000000000000 : ℝ)^811 := by
    have hnat : (4162497827 : ℕ)^1067*25000000000000^811 ≤ 7891134402491^811*10000000000^1067 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4162497827 10000000000 7891134402491 25000000000000 1067 811 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1067/256 : ℝ)) 1067 811 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4335577791/10000000000 : ℝ), (4515530659/10000000000 : ℝ), (4162497827/10000000000 : ℝ)] ![(16651269667803/50000000000000 : ℝ), (35132923041643/100000000000000 : ℝ), (7891134402491/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4335577791/10000000000 : ℝ)|^1067 ≤ (16651269667803/50000000000000 : ℝ)^811
        have hw : |(4335577791/10000000000 : ℝ)|=(4335577791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4515530659/10000000000 : ℝ)|^1067 ≤ (35132923041643/100000000000000 : ℝ)^811
        have hw : |(4515530659/10000000000 : ℝ)|=(4515530659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4162497827/10000000000 : ℝ)|^1067 ≤ (7891134402491/25000000000000 : ℝ)^811
        have hw : |(4162497827/10000000000 : ℝ)|=(4162497827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1308_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153390473/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5501/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (691/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1837/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14753/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5501/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14753/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5501/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14753/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5501/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14753/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5501/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14753/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5501/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14753/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5501/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5501/50000 : ℝ) ^ (4267/1024 : ℝ) ≤ (10134908098421607/100000000000000000000 : ℝ) := by
    have hpowers : (5501/50000 : ℝ)^4267 ≤ (10134908098421607/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5501 : ℕ)^4267*100000000000000000000^1024 ≤ 10134908098421607^1024*50000^4267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5501 50000 10134908098421607 100000000000000000000 4267 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5501/50000 : ℝ)) (X := (10134908098421607/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14753/100000 : ℝ) ^ (4267/1024 : ℝ) ≤ (1720683064624417/5000000000000000000 : ℝ) := by
    have hpowers : (14753/100000 : ℝ)^4267 ≤ (1720683064624417/5000000000000000000 : ℝ)^1024 := by
      have hnat : (14753 : ℕ)^4267*5000000000000000000^1024 ≤ 1720683064624417^1024*100000^4267 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14753 100000 1720683064624417 5000000000000000000 4267 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14753/100000 : ℝ)) (X := (1720683064624417/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010134908098421607/50000000000000000000 : ℝ) ≤ (10000486400121317/10000000000000000 : ℝ) ^ (4267/1024 : ℝ) := by
    have hpowers : (50010134908098421607/50000000000000000000 : ℝ)^1024 ≤ (10000486400121317/10000000000000000 : ℝ)^4267 := by
      have hnat : (50010134908098421607 : ℕ)^1024*10000000000000000^4267 ≤ 10000486400121317^4267*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010134908098421607 50000000000000000000 10000486400121317 10000000000000000 1024 4267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000486400121317/10000000000000000 : ℝ)) (X := (50010134908098421607/50000000000000000000 : ℝ)) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044548569390909947/100000000000000000000 : ℝ) ≤ (10001068901207057/10000000000000000 : ℝ) ^ (4267/1024 : ℝ) := by
    have hpowers : (100044548569390909947/100000000000000000000 : ℝ)^1024 ≤ (10001068901207057/10000000000000000 : ℝ)^4267 := by
      have hnat : (100044548569390909947 : ℕ)^1024*10000000000000000^4267 ≤ 10001068901207057^4267*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044548569390909947 100000000000000000000 10001068901207057 10000000000000000 1024 4267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001068901207057/10000000000000000 : ℝ)) (X := (100044548569390909947/100000000000000000000 : ℝ)) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501720683064624417/2500000000000000000 : ℝ) ≤ (10001651402292797/10000000000000000 : ℝ) ^ (4267/1024 : ℝ) := by
    have hpowers : (2501720683064624417/2500000000000000000 : ℝ)^1024 ≤ (10001651402292797/10000000000000000 : ℝ)^4267 := by
      have hnat : (2501720683064624417 : ℕ)^1024*10000000000000000^4267 ≤ 10001651402292797^4267*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501720683064624417 2500000000000000000 10001651402292797 10000000000000000 1024 4267 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001651402292797/10000000000000000 : ℝ)) (X := (2501720683064624417/2500000000000000000 : ℝ)) (by norm_num) 4267 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10134908098421607/100000000000000000000 : ℝ) ≤ ((37499007132964437107/37510000000000000000 : ℝ)+2*(29125054287/18755000000000 : ℝ)*(5501/50000 : ℝ))^(4267/1024 : ℝ) := by
    rw [show (37499007132964437107/37510000000000000000 : ℝ)+2*(29125054287/18755000000000 : ℝ)*(5501/50000 : ℝ)=(10000486400121317/10000000000000000 : ℝ) by norm_num, show 1+2*(10134908098421607/100000000000000000000 : ℝ)=(50010134908098421607/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1720683064624417/5000000000000000000 : ℝ)+(10134908098421607/100000000000000000000 : ℝ) ≤ ((37499007132964437107/37510000000000000000 : ℝ)+(29125054287/18755000000000 : ℝ)*((14753/100000 : ℝ)+(5501/50000 : ℝ)))^(4267/1024 : ℝ) := by
    rw [show (37499007132964437107/37510000000000000000 : ℝ)+(29125054287/18755000000000 : ℝ)*((14753/100000 : ℝ)+(5501/50000 : ℝ))=(10001068901207057/10000000000000000 : ℝ) by norm_num, show 1+(1720683064624417/5000000000000000000 : ℝ)+(10134908098421607/100000000000000000000 : ℝ)=(100044548569390909947/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1720683064624417/5000000000000000000 : ℝ) ≤ ((37499007132964437107/37510000000000000000 : ℝ)+2*(29125054287/18755000000000 : ℝ)*(14753/100000 : ℝ))^(4267/1024 : ℝ) := by
    rw [show (37499007132964437107/37510000000000000000 : ℝ)+2*(29125054287/18755000000000 : ℝ)*(14753/100000 : ℝ)=(10001651402292797/10000000000000000 : ℝ) by norm_num, show 1+2*(1720683064624417/5000000000000000000 : ℝ)=(2501720683064624417/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37499007132964437107/37510000000000000000 : ℝ)*(X 1 0+X 2 0)+(29125054287/18755000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4267/1024 : ℝ)) (lo := (5501/50000 : ℝ)) (hi := (14753/100000 : ℝ)) (c := (37499007132964437107/37510000000000000000 : ℝ)) (alpha := (29125054287/18755000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37499007132964437107/37510000000000000000 : ℝ)*(X 0 1+X 2 1)+(29125054287/18755000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4267/1024 : ℝ)) (lo := (5501/50000 : ℝ)) (hi := (14753/100000 : ℝ)) (c := (37499007132964437107/37510000000000000000 : ℝ)) (alpha := (29125054287/18755000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37499007132964437107/37510000000000000000 : ℝ)*(X 0 2+X 1 2)+(29125054287/18755000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4267/1024 : ℝ)) (lo := (5501/50000 : ℝ)) (hi := (14753/100000 : ℝ)) (c := (37499007132964437107/37510000000000000000 : ℝ)) (alpha := (29125054287/18755000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-103682441/500000000 : ℝ)*X 0 0+(1353746373/2500000000 : ℝ)*X 0 1+(2621509553/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069937901/2000000000 : ℝ)*X 1 0+(-54032627/250000000 : ℝ)*X 1 1+(5243019091/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069937897/2000000000 : ℝ)*X 2 0+(1048603821/2000000000 : ℝ)*X 2 1+(-2161305089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((433555133/1000000000 : ℝ)*X 0 0+(260075881/625000000 : ℝ)*X 0 1+(4516807827/10000000000 : ℝ)*X 0 2+(433555133/1000000000 : ℝ)*X 1 0+(260075881/625000000 : ℝ)*X 1 1+(4516807827/10000000000 : ℝ)*X 1 2+(433555133/1000000000 : ℝ)*X 2 0+(260075881/625000000 : ℝ)*X 2 1+(4516807827/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-103683103/500000000 : ℝ)*X 0 0+(5243636329/10000000000 : ℝ)*X 0 1+(5414364723/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305573819/10000000000 : ℝ)*X 1 0+(-1989959331/10000000000 : ℝ)*X 1 1+(5414364723/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305574043/10000000000 : ℝ)*X 2 0+(270718211/500000000 : ℝ)*X 2 1+(-497489929/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4335577791/10000000000 : ℝ)*X 0 0+(4515530659/10000000000 : ℝ)*X 0 1+(4162497827/10000000000 : ℝ)*X 0 2+(4335577791/10000000000 : ℝ)*X 1 0+(4515530659/10000000000 : ℝ)*X 1 1+(4162497827/10000000000 : ℝ)*X 1 2+(4335577791/10000000000 : ℝ)*X 2 0+(4515530659/10000000000 : ℝ)*X 2 1+(4162497827/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1308_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3938345903197722218156813169/468875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1608994177/100000000000000 : ℝ)*(base19) + (741541403/50000000000000 : ℝ)*(base23) + (27864183/50000000000000 : ℝ)*(lower2) + (42165207/20000000000000 : ℝ)*(upper3) + (14905597/12500000000000 : ℝ)*(upper5) + (2156846529021311/50000000000000 : ℝ)*(major0) + (2156846529021311/50000000000000 : ℝ)*(major1) + (2156846529021311/50000000000000 : ℝ)*(major2) + (5815123875843497/100000000000000 : ℝ)*(sp0) + (5815154123321599/100000000000000 : ℝ)*(sp1) + (581515424923297/10000000000000 : ℝ)*(sp2) + (1406106594420163/50000000000000 : ℝ)*(sp3) + (31856472279/100000000000000 : ℝ)*(sp4) + (16914943643/100000000000000 : ℝ)*(sp7) + (281223010378397/10000000000000 : ℝ)*(f.failure) + (45430904158717/781250000000 : ℝ)*(f.sum) + (24610618000393/3751000000000000000000000000 : ℝ)*base65 + (29476086385090733/60500000000000000000000000000000 : ℝ)*base68 + (779717015067909267/60500000000000000000000000000000 : ℝ)*base69 + (267256488544909267/60500000000000000000000000000000 : ℝ)*base71 + (7415826945193/3751000000000000000000000000 : ℝ)*base73 + (863946378912909267/60500000000000000000000000000000 : ℝ)*base75 + (568897270267409267/60500000000000000000000000000000 : ℝ)*base77 + (464051300247409267/60500000000000000000000000000000 : ℝ)*base79 + (16186610497273/3751000000000000000000000000 : ℝ)*base81 + (4811781/1000000000000000000000 : ℝ)*base89 + (4811781/1000000000000000000000 : ℝ)*base91 + (4811781/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (93434875147000281843/18755000000000000000000000 : ℝ) := by norm_num
    linear_combination (1783884421/100000000000000 : ℝ)*(base19) + (2364017401/100000000000000 : ℝ)*(base23) + (56901479/25000000000000 : ℝ)*(upper2) + (28372341/25000000000000 : ℝ)*(upper3) + (94078063/25000000000000 : ℝ)*(upper5) + (1086231867524159/25000000000000 : ℝ)*(major0) + (1086231867524159/25000000000000 : ℝ)*(major1) + (1086231867524159/25000000000000 : ℝ)*(major2) + (20558883243/50000000000000 : ℝ)*(sp1) + (29554084557/100000000000000 : ℝ)*(sp2) + (5857261989769173/100000000000000 : ℝ)*(sp4) + (2928609544059133/50000000000000 : ℝ)*(sp5) + (1171446014333443/20000000000000 : ℝ)*(sp6) + (708148196090483/25000000000000 : ℝ)*(sp7) + (708148196090483/25000000000000 : ℝ)*(f.failure) + (5857261989769173/100000000000000 : ℝ)*(f.sum) + (1416486553963/468875000000000000000000000 : ℝ)*base66 + (38564812377768323/30250000000000000000000000000000 : ℝ)*base67 + (87616798553268323/30250000000000000000000000000000 : ℝ)*base69 + (408037124449981677/30250000000000000000000000000000 : ℝ)*base72 + (2510058176317/1875500000000000000000000000 : ℝ)*base74 + (95584173012981677/30250000000000000000000000000000 : ℝ)*base76 + (219327826656481677/30250000000000000000000000000000 : ℝ)*base78 + (162214020620768323/30250000000000000000000000000000 : ℝ)*base79 + (8676600172627/3751000000000000000000000000 : ℝ)*base81 + (38168459/2500000000000000000000 : ℝ)*base89 + (38168459/2500000000000000000000 : ℝ)*base91 + (38168459/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1308_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153390473/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14753/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5501/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (691/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1837/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1308_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1308_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153390473/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8123/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (481/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (691/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1837/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1308_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1308_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1308_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4267/1024 : ℝ) ≤ p) (hpb : p ≤ (1067/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153390473/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8123/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (481/5000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (691/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1837/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1308_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
