-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1065_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:06:22.193235+00:00
-- url     : https://prove2.me/submissions/556bd55c-4976-4cdb-8d9b-fe636bf0dfdd

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
theorem support_rectangle_w1065_s6_0 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2204210927/10000000000 : ℝ)*x 0 + (1078987511/2000000000 : ℝ)*x 1 + (5263904243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2204210927/10000000000 : ℝ)^4129 ≤ (13386411590237/100000000000000 : ℝ)^3105 := by
    have hnat : (2204210927 : ℕ)^4129*100000000000000^3105 ≤ 13386411590237^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204210927 10000000000 13386411590237 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078987511/2000000000 : ℝ)^4129 ≤ (44014730539931/100000000000000 : ℝ)^3105 := by
    have hnat : (1078987511 : ℕ)^4129*100000000000000^3105 ≤ 44014730539931^3105*2000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078987511 2000000000 44014730539931 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263904243/10000000000 : ℝ)^4129 ≤ (166401788509/390625000000 : ℝ)^3105 := by
    have hnat : (5263904243 : ℕ)^4129*390625000000^3105 ≤ 166401788509^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263904243 10000000000 166401788509 390625000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2204210927/10000000000 : ℝ), (1078987511/2000000000 : ℝ), (5263904243/10000000000 : ℝ)] ![(13386411590237/100000000000000 : ℝ), (44014730539931/100000000000000 : ℝ), (166401788509/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2204210927/10000000000 : ℝ)|^4129 ≤ (13386411590237/100000000000000 : ℝ)^3105
        have hw : |(-2204210927/10000000000 : ℝ)|=(2204210927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078987511/2000000000 : ℝ)|^4129 ≤ (44014730539931/100000000000000 : ℝ)^3105
        have hw : |(1078987511/2000000000 : ℝ)|=(1078987511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263904243/10000000000 : ℝ)|^4129 ≤ (166401788509/390625000000 : ℝ)^3105
        have hw : |(5263904243/10000000000 : ℝ)|=(5263904243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s6_1 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069024463/2000000000 : ℝ)*x 0 + (-2270701293/10000000000 : ℝ)*x 1 + (5263904291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069024463/2000000000 : ℝ)^4129 ≤ (43475103130247/100000000000000 : ℝ)^3105 := by
    have hnat : (1069024463 : ℕ)^4129*100000000000000^3105 ≤ 43475103130247^3105*2000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069024463 2000000000 43475103130247 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2270701293/10000000000 : ℝ)^4129 ≤ (3481509620797/25000000000000 : ℝ)^3105 := by
    have hnat : (2270701293 : ℕ)^4129*25000000000000^3105 ≤ 3481509620797^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270701293 10000000000 3481509620797 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5263904291/10000000000 : ℝ)^4129 ≤ (5324857296857/12500000000000 : ℝ)^3105 := by
    have hnat : (5263904291 : ℕ)^4129*12500000000000^3105 ≤ 5324857296857^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263904291 10000000000 5324857296857 12500000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069024463/2000000000 : ℝ), (-2270701293/10000000000 : ℝ), (5263904291/10000000000 : ℝ)] ![(43475103130247/100000000000000 : ℝ), (3481509620797/25000000000000 : ℝ), (5324857296857/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069024463/2000000000 : ℝ)|^4129 ≤ (43475103130247/100000000000000 : ℝ)^3105
        have hw : |(1069024463/2000000000 : ℝ)|=(1069024463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2270701293/10000000000 : ℝ)|^4129 ≤ (3481509620797/25000000000000 : ℝ)^3105
        have hw : |(-2270701293/10000000000 : ℝ)|=(2270701293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5263904291/10000000000 : ℝ)|^4129 ≤ (5324857296857/12500000000000 : ℝ)^3105
        have hw : |(5263904291/10000000000 : ℝ)|=(5263904291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s6_2 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672561033/5000000000 : ℝ)*x 0 + (1052780887/2000000000 : ℝ)*x 1 + (-2270701433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672561033/5000000000 : ℝ)^4129 ≤ (21737550218533/50000000000000 : ℝ)^3105 := by
    have hnat : (2672561033 : ℕ)^4129*50000000000000^3105 ≤ 21737550218533^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672561033 5000000000 21737550218533 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052780887/2000000000 : ℝ)^4129 ≤ (21299429962257/50000000000000 : ℝ)^3105 := by
    have hnat : (1052780887 : ℕ)^4129*50000000000000^3105 ≤ 21299429962257^3105*2000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052780887 2000000000 21299429962257 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2270701433/10000000000 : ℝ)^4129 ≤ (6963019812479/50000000000000 : ℝ)^3105 := by
    have hnat : (2270701433 : ℕ)^4129*50000000000000^3105 ≤ 6963019812479^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270701433 10000000000 6963019812479 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672561033/5000000000 : ℝ), (1052780887/2000000000 : ℝ), (-2270701433/10000000000 : ℝ)] ![(21737550218533/50000000000000 : ℝ), (21299429962257/50000000000000 : ℝ), (6963019812479/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672561033/5000000000 : ℝ)|^4129 ≤ (21737550218533/50000000000000 : ℝ)^3105
        have hw : |(2672561033/5000000000 : ℝ)|=(2672561033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052780887/2000000000 : ℝ)|^4129 ≤ (21299429962257/50000000000000 : ℝ)^3105
        have hw : |(1052780887/2000000000 : ℝ)|=(1052780887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2270701433/10000000000 : ℝ)|^4129 ≤ (6963019812479/50000000000000 : ℝ)^3105
        have hw : |(-2270701433/10000000000 : ℝ)|=(2270701433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s6_3 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2187804033/5000000000 : ℝ)*x 0 + (1062284577/2500000000 : ℝ)*x 1 + (4505894487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187804033/5000000000 : ℝ)^4129 ≤ (33316259479733/100000000000000 : ℝ)^3105 := by
    have hnat : (2187804033 : ℕ)^4129*100000000000000^3105 ≤ 33316259479733^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187804033 5000000000 33316259479733 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1062284577/2500000000 : ℝ)^4129 ≤ (8010469548437/25000000000000 : ℝ)^3105 := by
    have hnat : (1062284577 : ℕ)^4129*25000000000000^3105 ≤ 8010469548437^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062284577 2500000000 8010469548437 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4505894487/10000000000 : ℝ)^4129 ≤ (17320931149633/50000000000000 : ℝ)^3105 := by
    have hnat : (4505894487 : ℕ)^4129*50000000000000^3105 ≤ 17320931149633^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505894487 10000000000 17320931149633 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187804033/5000000000 : ℝ), (1062284577/2500000000 : ℝ), (4505894487/10000000000 : ℝ)] ![(33316259479733/100000000000000 : ℝ), (8010469548437/25000000000000 : ℝ), (17320931149633/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187804033/5000000000 : ℝ)|^4129 ≤ (33316259479733/100000000000000 : ℝ)^3105
        have hw : |(2187804033/5000000000 : ℝ)|=(2187804033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1062284577/2500000000 : ℝ)|^4129 ≤ (8010469548437/25000000000000 : ℝ)^3105
        have hw : |(1062284577/2500000000 : ℝ)|=(1062284577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4505894487/10000000000 : ℝ)|^4129 ≤ (17320931149633/50000000000000 : ℝ)^3105
        have hw : |(4505894487/10000000000 : ℝ)|=(4505894487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s6_4 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2204216187/10000000000 : ℝ)*x 0 + (82253677/156250000 : ℝ)*x 1 + (2697302611/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2204216187/10000000000 : ℝ)^4129 ≤ (13386454069817/100000000000000 : ℝ)^3105 := by
    have hnat : (2204216187 : ℕ)^4129*100000000000000^3105 ≤ 13386454069817^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204216187 10000000000 13386454069817 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (82253677/156250000 : ℝ)^4129 ≤ (1065060521753/2500000000000 : ℝ)^3105 := by
    have hnat : (82253677 : ℕ)^4129*2500000000000^3105 ≤ 1065060521753^3105*156250000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82253677 156250000 1065060521753 2500000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697302611/5000000000 : ℝ)^4129 ≤ (22005562526357/50000000000000 : ℝ)^3105 := by
    have hnat : (2697302611 : ℕ)^4129*50000000000000^3105 ≤ 22005562526357^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697302611 5000000000 22005562526357 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2204216187/10000000000 : ℝ), (82253677/156250000 : ℝ), (2697302611/5000000000 : ℝ)] ![(13386454069817/100000000000000 : ℝ), (1065060521753/2500000000000 : ℝ), (22005562526357/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2204216187/10000000000 : ℝ)|^4129 ≤ (13386454069817/100000000000000 : ℝ)^3105
        have hw : |(-2204216187/10000000000 : ℝ)|=(2204216187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(82253677/156250000 : ℝ)|^4129 ≤ (1065060521753/2500000000000 : ℝ)^3105
        have hw : |(82253677/156250000 : ℝ)|=(82253677/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697302611/5000000000 : ℝ)|^4129 ≤ (22005562526357/50000000000000 : ℝ)^3105
        have hw : |(2697302611/5000000000 : ℝ)|=(2697302611/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s6_5 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312120257/10000000000 : ℝ)*x 0 + (-2140000279/10000000000 : ℝ)*x 1 + (2697302687/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312120257/10000000000 : ℝ)^4129 ≤ (43118517136363/100000000000000 : ℝ)^3105 := by
    have hnat : (5312120257 : ℕ)^4129*100000000000000^3105 ≤ 43118517136363^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312120257 10000000000 43118517136363 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2140000279/10000000000 : ℝ)^4129 ≤ (12870356148797/100000000000000 : ℝ)^3105 := by
    have hnat : (2140000279 : ℕ)^4129*100000000000000^3105 ≤ 12870356148797^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140000279 10000000000 12870356148797 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697302687/5000000000 : ℝ)^4129 ≤ (44011126701749/100000000000000 : ℝ)^3105 := by
    have hnat : (2697302687 : ℕ)^4129*100000000000000^3105 ≤ 44011126701749^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697302687 5000000000 44011126701749 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312120257/10000000000 : ℝ), (-2140000279/10000000000 : ℝ), (2697302687/5000000000 : ℝ)] ![(43118517136363/100000000000000 : ℝ), (12870356148797/100000000000000 : ℝ), (44011126701749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312120257/10000000000 : ℝ)|^4129 ≤ (43118517136363/100000000000000 : ℝ)^3105
        have hw : |(5312120257/10000000000 : ℝ)|=(5312120257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2140000279/10000000000 : ℝ)|^4129 ≤ (12870356148797/100000000000000 : ℝ)^3105
        have hw : |(-2140000279/10000000000 : ℝ)|=(2140000279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697302687/5000000000 : ℝ)|^4129 ≤ (44011126701749/100000000000000 : ℝ)^3105
        have hw : |(2697302687/5000000000 : ℝ)|=(2697302687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s6_6 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312119959/10000000000 : ℝ)*x 0 + (134865143/250000000 : ℝ)*x 1 + (-2140000211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312119959/10000000000 : ℝ)^4129 ≤ (21559256959887/50000000000000 : ℝ)^3105 := by
    have hnat : (5312119959 : ℕ)^4129*50000000000000^3105 ≤ 21559256959887^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312119959 10000000000 21559256959887 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (134865143/250000000 : ℝ)^4129 ≤ (44011130455471/100000000000000 : ℝ)^3105 := by
    have hnat : (134865143 : ℕ)^4129*100000000000000^3105 ≤ 44011130455471^3105*250000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134865143 250000000 44011130455471 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2140000211/10000000000 : ℝ)^4129 ≤ (80439722531/625000000000 : ℝ)^3105 := by
    have hnat : (2140000211 : ℕ)^4129*625000000000^3105 ≤ 80439722531^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140000211 10000000000 80439722531 625000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312119959/10000000000 : ℝ), (134865143/250000000 : ℝ), (-2140000211/10000000000 : ℝ)] ![(21559256959887/50000000000000 : ℝ), (44011130455471/100000000000000 : ℝ), (80439722531/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312119959/10000000000 : ℝ)|^4129 ≤ (21559256959887/50000000000000 : ℝ)^3105
        have hw : |(5312119959/10000000000 : ℝ)|=(5312119959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(134865143/250000000 : ℝ)|^4129 ≤ (44011130455471/100000000000000 : ℝ)^3105
        have hw : |(134865143/250000000 : ℝ)|=(134865143/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2140000211/10000000000 : ℝ)|^4129 ≤ (80439722531/625000000000 : ℝ)^3105
        have hw : |(-2140000211/10000000000 : ℝ)|=(2140000211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s6_7 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (875123663/2000000000 : ℝ)*x 0 + (112631147/250000000 : ℝ)*x 1 + (531223651/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875123663/2000000000 : ℝ)^4129 ≤ (8329090813087/25000000000000 : ℝ)^3105 := by
    have hnat : (875123663 : ℕ)^4129*25000000000000^3105 ≤ 8329090813087^3105*2000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875123663 2000000000 8329090813087 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112631147/250000000 : ℝ)^4129 ≤ (8658807840901/25000000000000 : ℝ)^3105 := by
    have hnat : (112631147 : ℕ)^4129*25000000000000^3105 ≤ 8658807840901^3105*250000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112631147 250000000 8658807840901 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (531223651/1250000000 : ℝ)^4129 ≤ (8012101343541/25000000000000 : ℝ)^3105 := by
    have hnat : (531223651 : ℕ)^4129*25000000000000^3105 ≤ 8012101343541^3105*1250000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531223651 1250000000 8012101343541 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875123663/2000000000 : ℝ), (112631147/250000000 : ℝ), (531223651/1250000000 : ℝ)] ![(8329090813087/25000000000000 : ℝ), (8658807840901/25000000000000 : ℝ), (8012101343541/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875123663/2000000000 : ℝ)|^4129 ≤ (8329090813087/25000000000000 : ℝ)^3105
        have hw : |(875123663/2000000000 : ℝ)|=(875123663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(112631147/250000000 : ℝ)|^4129 ≤ (8658807840901/25000000000000 : ℝ)^3105
        have hw : |(112631147/250000000 : ℝ)|=(112631147/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(531223651/1250000000 : ℝ)|^4129 ≤ (8012101343541/25000000000000 : ℝ)^3105
        have hw : |(531223651/1250000000 : ℝ)|=(531223651/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1065_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11197/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11239/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7007/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7029/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11197/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7029/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11197/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7029/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11197/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7029/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11197/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7029/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11197/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7029/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11197/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11197/100000 : ℝ) ^ (8257/2048 : ℝ) ≤ (1466313504795919/10000000000000000000 : ℝ) := by
    have hpowers : (11197/100000 : ℝ)^8257 ≤ (1466313504795919/10000000000000000000 : ℝ)^2048 := by
      have hnat : (11197 : ℕ)^8257*10000000000000000000^2048 ≤ 1466313504795919^2048*100000^8257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11197 100000 1466313504795919 10000000000000000000 8257 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11197/100000 : ℝ)) (X := (1466313504795919/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7029/50000 : ℝ) ^ (8257/2048 : ℝ) ≤ (7339740562862143/20000000000000000000 : ℝ) := by
    have hpowers : (7029/50000 : ℝ)^8257 ≤ (7339740562862143/20000000000000000000 : ℝ)^2048 := by
      have hnat : (7029 : ℕ)^8257*20000000000000000000^2048 ≤ 7339740562862143^2048*50000^8257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7029 50000 7339740562862143 20000000000000000000 8257 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7029/50000 : ℝ)) (X := (7339740562862143/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001466313504795919/5000000000000000000 : ℝ) ≤ (10000727305073601/10000000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (5001466313504795919/5000000000000000000 : ℝ)^2048 ≤ (10000727305073601/10000000000000000 : ℝ)^8257 := by
      have hnat : (5001466313504795919 : ℕ)^2048*10000000000000000^8257 ≤ 10000727305073601^8257*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001466313504795919 5000000000000000000 10000727305073601 10000000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000727305073601/10000000000000000 : ℝ)) (X := (5001466313504795919/5000000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010272367572453981/20000000000000000000 : ℝ) ≤ (10001273691858237/10000000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (20010272367572453981/20000000000000000000 : ℝ)^2048 ≤ (10001273691858237/10000000000000000 : ℝ)^8257 := by
      have hnat : (20010272367572453981 : ℕ)^2048*10000000000000000^8257 ≤ 10001273691858237^8257*20000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010272367572453981 20000000000000000000 10001273691858237 10000000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001273691858237/10000000000000000 : ℝ)) (X := (20010272367572453981/20000000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007339740562862143/10000000000000000000 : ℝ) ≤ (10001820078642873/10000000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (10007339740562862143/10000000000000000000 : ℝ)^2048 ≤ (10001820078642873/10000000000000000 : ℝ)^8257 := by
      have hnat : (10007339740562862143 : ℕ)^2048*10000000000000000^8257 ≤ 10001820078642873^8257*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007339740562862143 10000000000000000000 10001820078642873 10000000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001820078642873/10000000000000000 : ℝ)) (X := (10007339740562862143/10000000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1466313504795919/10000000000000000000 : ℝ) ≤ ((28599845034160433877/28610000000000000000 : ℝ)+2*(136596696159/71525000000000 : ℝ)*(11197/100000 : ℝ))^(8257/2048 : ℝ) := by
    rw [show (28599845034160433877/28610000000000000000 : ℝ)+2*(136596696159/71525000000000 : ℝ)*(11197/100000 : ℝ)=(10000727305073601/10000000000000000 : ℝ) by norm_num, show 1+2*(1466313504795919/10000000000000000000 : ℝ)=(5001466313504795919/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7339740562862143/20000000000000000000 : ℝ)+(1466313504795919/10000000000000000000 : ℝ) ≤ ((28599845034160433877/28610000000000000000 : ℝ)+(136596696159/71525000000000 : ℝ)*((7029/50000 : ℝ)+(11197/100000 : ℝ)))^(8257/2048 : ℝ) := by
    rw [show (28599845034160433877/28610000000000000000 : ℝ)+(136596696159/71525000000000 : ℝ)*((7029/50000 : ℝ)+(11197/100000 : ℝ))=(10001273691858237/10000000000000000 : ℝ) by norm_num, show 1+(7339740562862143/20000000000000000000 : ℝ)+(1466313504795919/10000000000000000000 : ℝ)=(20010272367572453981/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7339740562862143/20000000000000000000 : ℝ) ≤ ((28599845034160433877/28610000000000000000 : ℝ)+2*(136596696159/71525000000000 : ℝ)*(7029/50000 : ℝ))^(8257/2048 : ℝ) := by
    rw [show (28599845034160433877/28610000000000000000 : ℝ)+2*(136596696159/71525000000000 : ℝ)*(7029/50000 : ℝ)=(10001820078642873/10000000000000000 : ℝ) by norm_num, show 1+2*(7339740562862143/20000000000000000000 : ℝ)=(10007339740562862143/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28599845034160433877/28610000000000000000 : ℝ)*(X 1 0+X 2 0)+(136596696159/71525000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (11197/100000 : ℝ)) (hi := (7029/50000 : ℝ)) (c := (28599845034160433877/28610000000000000000 : ℝ)) (alpha := (136596696159/71525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28599845034160433877/28610000000000000000 : ℝ)*(X 0 1+X 2 1)+(136596696159/71525000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (11197/100000 : ℝ)) (hi := (7029/50000 : ℝ)) (c := (28599845034160433877/28610000000000000000 : ℝ)) (alpha := (136596696159/71525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28599845034160433877/28610000000000000000 : ℝ)*(X 0 2+X 1 2)+(136596696159/71525000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (11197/100000 : ℝ)) (hi := (7029/50000 : ℝ)) (c := (28599845034160433877/28610000000000000000 : ℝ)) (alpha := (136596696159/71525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2204210927/10000000000 : ℝ)*X 0 0+(1078987511/2000000000 : ℝ)*X 0 1+(5263904243/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069024463/2000000000 : ℝ)*X 1 0+(-2270701293/10000000000 : ℝ)*X 1 1+(5263904291/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672561033/5000000000 : ℝ)*X 2 0+(1052780887/2000000000 : ℝ)*X 2 1+(-2270701433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2187804033/5000000000 : ℝ)*X 0 0+(1062284577/2500000000 : ℝ)*X 0 1+(4505894487/10000000000 : ℝ)*X 0 2+(2187804033/5000000000 : ℝ)*X 1 0+(1062284577/2500000000 : ℝ)*X 1 1+(4505894487/10000000000 : ℝ)*X 1 2+(2187804033/5000000000 : ℝ)*X 2 0+(1062284577/2500000000 : ℝ)*X 2 1+(4505894487/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2204216187/10000000000 : ℝ)*X 0 0+(82253677/156250000 : ℝ)*X 0 1+(2697302611/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312120257/10000000000 : ℝ)*X 1 0+(-2140000279/10000000000 : ℝ)*X 1 1+(2697302687/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312119959/10000000000 : ℝ)*X 2 0+(134865143/250000000 : ℝ)*X 2 1+(-2140000211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((875123663/2000000000 : ℝ)*X 0 0+(112631147/250000000 : ℝ)*X 0 1+(531223651/1250000000 : ℝ)*X 0 2+(875123663/2000000000 : ℝ)*X 1 0+(112631147/250000000 : ℝ)*X 1 1+(531223651/1250000000 : ℝ)*X 1 2+(875123663/2000000000 : ℝ)*X 2 0+(112631147/250000000 : ℝ)*X 2 1+(531223651/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5433724540821092924042689929/1430500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (953891531/100000000000000 : ℝ)*(base19) + (634774149/100000000000000 : ℝ)*(base23) + (23963817/100000000000000 : ℝ)*(upper2) + (109503899/50000000000000 : ℝ)*(upper3) + (5763239643607241/100000000000000 : ℝ)*(major0) + (5763239643607241/100000000000000 : ℝ)*(major1) + (5763239643607241/100000000000000 : ℝ)*(major2) + (7631682570090051/100000000000000 : ℝ)*(sp0) + (3815851113933873/50000000000000 : ℝ)*(sp1) + (381585059072289/5000000000000 : ℝ)*(sp2) + (1947379815195989/50000000000000 : ℝ)*(sp3) + (824466769/4000000000000 : ℝ)*(sp4) + (1365539347/100000000000000 : ℝ)*(sp6) + (8174223623/50000000000000 : ℝ)*(sp7) + (486846997354903/12500000000000 : ℝ)*(f.failure) + (1907925795439819/25000000000000 : ℝ)*(f.sum) + (47474077688023/7152500000000000000000000000 : ℝ)*base65 + (13659622817317503357/2861000000000000000000000000000000 : ℝ)*base67 + (8042034888350496643/2861000000000000000000000000000000 : ℝ)*base70 + (24857373059758503357/2861000000000000000000000000000000 : ℝ)*base71 + (16898059713423/7152500000000000000000000000 : ℝ)*base73 + (60333157712073496643/2861000000000000000000000000000000 : ℝ)*base76 + (40748064391315503357/2861000000000000000000000000000000 : ℝ)*base77 + (1934806984182503357/2861000000000000000000000000000000 : ℝ)*base79 + (49478969965309/14305000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (347451/250000000000000000000 : ℝ)*base89 + (347451/250000000000000000000 : ℝ)*base91 + (347451/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (655434067630803151879428339/143050000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (211823421/20000000000000 : ℝ)*(base19) + (96567047/12500000000000 : ℝ)*(base23) + (5138983/12500000000000 : ℝ)*(upper2) + (255398137/100000000000000 : ℝ)*(upper3) + (17130601/25000000000000 : ℝ)*(upper5) + (1158502851568131/20000000000000 : ℝ)*(major0) + (1158502851568131/20000000000000 : ℝ)*(major1) + (1158502851568131/20000000000000 : ℝ)*(major2) + (13349476661/50000000000000 : ℝ)*(sp1) + (37374883683/100000000000000 : ℝ)*(sp2) + (7670468708376239/100000000000000 : ℝ)*(sp4) + (7670440950305813/100000000000000 : ℝ)*(sp5) + (383521528047809/5000000000000 : ℝ)*(sp6) + (391455965457663/10000000000000 : ℝ)*(sp7) + (391455965457663/10000000000000 : ℝ)*(f.failure) + (7670468708376239/100000000000000 : ℝ)*(f.sum) + (7836535452539/2861000000000000000000000000 : ℝ)*base65 + (5563202864135173887/572200000000000000000000000000000 : ℝ)*base67 + (2367824458441973887/572200000000000000000000000000000 : ℝ)*base69 + (754547187858626113/572200000000000000000000000000000 : ℝ)*base72 + (1248339651131/2861000000000000000000000000 : ℝ)*base74 + (8897986173868773887/572200000000000000000000000000000 : ℝ)*base75 + (5001034470831973887/572200000000000000000000000000000 : ℝ)*base77 + (13007174498636573887/572200000000000000000000000000000 : ℝ)*base79 + (471063691987/572200000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1966371/200000000000000000000 : ℝ)*base89 + (1966371/200000000000000000000 : ℝ)*base91 + (1966371/200000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1065_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11197/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11239/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7007/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1065_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1065_s7_0 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-275531491/1250000000 : ℝ)*x 0 + (1078894019/2000000000 : ℝ)*x 1 + (5264344727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (275531491/1250000000 : ℝ)^4129 ≤ (13386742713797/100000000000000 : ℝ)^3105 := by
    have hnat : (275531491 : ℕ)^4129*100000000000000^3105 ≤ 13386742713797^3105*1250000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275531491 1250000000 13386742713797 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078894019/2000000000 : ℝ)^4129 ≤ (11002414769549/25000000000000 : ℝ)^3105 := by
    have hnat : (1078894019 : ℕ)^4129*25000000000000^3105 ≤ 11002414769549^3105*2000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078894019 2000000000 11002414769549 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264344727/10000000000 : ℝ)^4129 ≤ (21301799098557/50000000000000 : ℝ)^3105 := by
    have hnat : (5264344727 : ℕ)^4129*50000000000000^3105 ≤ 21301799098557^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264344727 10000000000 21301799098557 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-275531491/1250000000 : ℝ), (1078894019/2000000000 : ℝ), (5264344727/10000000000 : ℝ)] ![(13386742713797/100000000000000 : ℝ), (11002414769549/25000000000000 : ℝ), (21301799098557/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-275531491/1250000000 : ℝ)|^4129 ≤ (13386742713797/100000000000000 : ℝ)^3105
        have hw : |(-275531491/1250000000 : ℝ)|=(275531491/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078894019/2000000000 : ℝ)|^4129 ≤ (11002414769549/25000000000000 : ℝ)^3105
        have hw : |(1078894019/2000000000 : ℝ)|=(1078894019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264344727/10000000000 : ℝ)|^4129 ≤ (21301799098557/50000000000000 : ℝ)^3105
        have hw : |(5264344727/10000000000 : ℝ)|=(5264344727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s7_1 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345005461/10000000000 : ℝ)*x 0 + (-1135137407/5000000000 : ℝ)*x 1 + (5264344923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345005461/10000000000 : ℝ)^4129 ≤ (21736919621591/50000000000000 : ℝ)^3105 := by
    have hnat : (5345005461 : ℕ)^4129*50000000000000^3105 ≤ 21736919621591^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345005461 10000000000 21736919621591 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1135137407/5000000000 : ℝ)^4129 ≤ (2784512087853/20000000000000 : ℝ)^3105 := by
    have hnat : (1135137407 : ℕ)^4129*20000000000000^3105 ≤ 2784512087853^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135137407 5000000000 2784512087853 20000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264344923/10000000000 : ℝ)^4129 ≤ (10650900076607/25000000000000 : ℝ)^3105 := by
    have hnat : (5264344923 : ℕ)^4129*25000000000000^3105 ≤ 10650900076607^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264344923 10000000000 10650900076607 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345005461/10000000000 : ℝ), (-1135137407/5000000000 : ℝ), (5264344923/10000000000 : ℝ)] ![(21736919621591/50000000000000 : ℝ), (2784512087853/20000000000000 : ℝ), (10650900076607/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345005461/10000000000 : ℝ)|^4129 ≤ (21736919621591/50000000000000 : ℝ)^3105
        have hw : |(5345005461/10000000000 : ℝ)|=(5345005461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1135137407/5000000000 : ℝ)|^4129 ≤ (2784512087853/20000000000000 : ℝ)^3105
        have hw : |(-1135137407/5000000000 : ℝ)|=(1135137407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264344923/10000000000 : ℝ)|^4129 ≤ (10650900076607/25000000000000 : ℝ)^3105
        have hw : |(5264344923/10000000000 : ℝ)|=(5264344923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s7_2 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267250277/500000000 : ℝ)*x 0 + (5264344767/10000000000 : ℝ)*x 1 + (-1135137457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267250277/500000000 : ℝ)^4129 ≤ (43473840097639/100000000000000 : ℝ)^3105 := by
    have hnat : (267250277 : ℕ)^4129*100000000000000^3105 ≤ 43473840097639^3105*500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267250277 500000000 43473840097639 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264344767/10000000000 : ℝ)^4129 ≤ (21301799313793/50000000000000 : ℝ)^3105 := by
    have hnat : (5264344767 : ℕ)^4129*50000000000000^3105 ≤ 21301799313793^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264344767 10000000000 21301799313793 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1135137457/5000000000 : ℝ)^4129 ≤ (2784512250953/20000000000000 : ℝ)^3105 := by
    have hnat : (1135137457 : ℕ)^4129*20000000000000^3105 ≤ 2784512250953^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135137457 5000000000 2784512250953 20000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267250277/500000000 : ℝ), (5264344767/10000000000 : ℝ), (-1135137457/5000000000 : ℝ)] ![(43473840097639/100000000000000 : ℝ), (21301799313793/50000000000000 : ℝ), (2784512250953/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267250277/500000000 : ℝ)|^4129 ≤ (43473840097639/100000000000000 : ℝ)^3105
        have hw : |(267250277/500000000 : ℝ)|=(267250277/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264344767/10000000000 : ℝ)|^4129 ≤ (21301799313793/50000000000000 : ℝ)^3105
        have hw : |(5264344767/10000000000 : ℝ)|=(5264344767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1135137457/5000000000 : ℝ)|^4129 ≤ (2784512250953/20000000000000 : ℝ)^3105
        have hw : |(-1135137457/5000000000 : ℝ)|=(1135137457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s7_3 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (136738479/312500000 : ℝ)*x 0 + (2125012547/5000000000 : ℝ)*x 1 + (2252500799/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136738479/312500000 : ℝ)^4129 ≤ (1665824750549/5000000000000 : ℝ)^3105 := by
    have hnat : (136738479 : ℕ)^4129*5000000000000^3105 ≤ 1665824750549^3105*312500000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136738479 312500000 1665824750549 5000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2125012547/5000000000 : ℝ)^4129 ≤ (4006346363017/12500000000000 : ℝ)^3105 := by
    have hnat : (2125012547 : ℕ)^4129*12500000000000^3105 ≤ 4006346363017^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125012547 5000000000 4006346363017 12500000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2252500799/5000000000 : ℝ)^4129 ≤ (17316367032549/50000000000000 : ℝ)^3105 := by
    have hnat : (2252500799 : ℕ)^4129*50000000000000^3105 ≤ 17316367032549^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252500799 5000000000 17316367032549 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136738479/312500000 : ℝ), (2125012547/5000000000 : ℝ), (2252500799/5000000000 : ℝ)] ![(1665824750549/5000000000000 : ℝ), (4006346363017/12500000000000 : ℝ), (17316367032549/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136738479/312500000 : ℝ)|^4129 ≤ (1665824750549/5000000000000 : ℝ)^3105
        have hw : |(136738479/312500000 : ℝ)|=(136738479/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2125012547/5000000000 : ℝ)|^4129 ≤ (4006346363017/12500000000000 : ℝ)^3105
        have hw : |(2125012547/5000000000 : ℝ)|=(2125012547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2252500799/5000000000 : ℝ)|^4129 ≤ (17316367032549/50000000000000 : ℝ)^3105
        have hw : |(2252500799/5000000000 : ℝ)|=(2252500799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s7_4 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2204256917/10000000000 : ℝ)*x 0 + (5264671237/10000000000 : ℝ)*x 1 + (2697071241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2204256917/10000000000 : ℝ)^4129 ≤ (13386783005037/100000000000000 : ℝ)^3105 := by
    have hnat : (2204256917 : ℕ)^4129*100000000000000^3105 ≤ 13386783005037^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204256917 10000000000 13386783005037 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264671237/10000000000 : ℝ)^4129 ≤ (42607112070967/100000000000000 : ℝ)^3105 := by
    have hnat : (5264671237 : ℕ)^4129*100000000000000^3105 ≤ 42607112070967^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264671237 10000000000 42607112070967 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697071241/5000000000 : ℝ)^4129 ≤ (44006104899411/100000000000000 : ℝ)^3105 := by
    have hnat : (2697071241 : ℕ)^4129*100000000000000^3105 ≤ 44006104899411^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697071241 5000000000 44006104899411 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2204256917/10000000000 : ℝ), (5264671237/10000000000 : ℝ), (2697071241/5000000000 : ℝ)] ![(13386783005037/100000000000000 : ℝ), (42607112070967/100000000000000 : ℝ), (44006104899411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2204256917/10000000000 : ℝ)|^4129 ≤ (13386783005037/100000000000000 : ℝ)^3105
        have hw : |(-2204256917/10000000000 : ℝ)|=(2204256917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264671237/10000000000 : ℝ)|^4129 ≤ (42607112070967/100000000000000 : ℝ)^3105
        have hw : |(5264671237/10000000000 : ℝ)|=(5264671237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697071241/5000000000 : ℝ)|^4129 ≤ (44006104899411/100000000000000 : ℝ)^3105
        have hw : |(2697071241/5000000000 : ℝ)|=(2697071241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s7_5 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (531223207/1000000000 : ℝ)*x 0 + (-428095453/2000000000 : ℝ)*x 1 + (2697071241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531223207/1000000000 : ℝ)^4129 ≤ (8623944808227/20000000000000 : ℝ)^3105 := by
    have hnat : (531223207 : ℕ)^4129*20000000000000^3105 ≤ 8623944808227^3105*1000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531223207 1000000000 8623944808227 20000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (428095453/2000000000 : ℝ)^4129 ≤ (2574834207033/20000000000000 : ℝ)^3105 := by
    have hnat : (428095453 : ℕ)^4129*20000000000000^3105 ≤ 2574834207033^3105*2000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428095453 2000000000 2574834207033 20000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697071241/5000000000 : ℝ)^4129 ≤ (44006104899411/100000000000000 : ℝ)^3105 := by
    have hnat : (2697071241 : ℕ)^4129*100000000000000^3105 ≤ 44006104899411^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697071241 5000000000 44006104899411 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531223207/1000000000 : ℝ), (-428095453/2000000000 : ℝ), (2697071241/5000000000 : ℝ)] ![(8623944808227/20000000000000 : ℝ), (2574834207033/20000000000000 : ℝ), (44006104899411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531223207/1000000000 : ℝ)|^4129 ≤ (8623944808227/20000000000000 : ℝ)^3105
        have hw : |(531223207/1000000000 : ℝ)|=(531223207/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-428095453/2000000000 : ℝ)|^4129 ≤ (2574834207033/20000000000000 : ℝ)^3105
        have hw : |(-428095453/2000000000 : ℝ)|=(428095453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697071241/5000000000 : ℝ)|^4129 ≤ (44006104899411/100000000000000 : ℝ)^3105
        have hw : |(2697071241/5000000000 : ℝ)|=(2697071241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s7_6 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (531223207/1000000000 : ℝ)*x 0 + (2697071241/5000000000 : ℝ)*x 1 + (-428095453/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531223207/1000000000 : ℝ)^4129 ≤ (8623944808227/20000000000000 : ℝ)^3105 := by
    have hnat : (531223207 : ℕ)^4129*20000000000000^3105 ≤ 8623944808227^3105*1000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531223207 1000000000 8623944808227 20000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697071241/5000000000 : ℝ)^4129 ≤ (44006104899411/100000000000000 : ℝ)^3105 := by
    have hnat : (2697071241 : ℕ)^4129*100000000000000^3105 ≤ 44006104899411^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697071241 5000000000 44006104899411 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (428095453/2000000000 : ℝ)^4129 ≤ (2574834207033/20000000000000 : ℝ)^3105 := by
    have hnat : (428095453 : ℕ)^4129*20000000000000^3105 ≤ 2574834207033^3105*2000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428095453 2000000000 2574834207033 20000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531223207/1000000000 : ℝ), (2697071241/5000000000 : ℝ), (-428095453/2000000000 : ℝ)] ![(8623944808227/20000000000000 : ℝ), (44006104899411/100000000000000 : ℝ), (2574834207033/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531223207/1000000000 : ℝ)|^4129 ≤ (8623944808227/20000000000000 : ℝ)^3105
        have hw : |(531223207/1000000000 : ℝ)|=(531223207/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697071241/5000000000 : ℝ)|^4129 ≤ (44006104899411/100000000000000 : ℝ)^3105
        have hw : |(2697071241/5000000000 : ℝ)|=(2697071241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-428095453/2000000000 : ℝ)|^4129 ≤ (2574834207033/20000000000000 : ℝ)^3105
        have hw : |(-428095453/2000000000 : ℝ)|=(428095453/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s7_7 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2187820651/5000000000 : ℝ)*x 0 + (4504362119/10000000000 : ℝ)*x 1 + (2125333439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187820651/5000000000 : ℝ)^4129 ≤ (8329148999839/25000000000000 : ℝ)^3105 := by
    have hnat : (2187820651 : ℕ)^4129*25000000000000^3105 ≤ 8329148999839^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187820651 5000000000 8329148999839 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4504362119/10000000000 : ℝ)^4129 ≤ (34626196873281/100000000000000 : ℝ)^3105 := by
    have hnat : (4504362119 : ℕ)^4129*100000000000000^3105 ≤ 34626196873281^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504362119 10000000000 34626196873281 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2125333439/5000000000 : ℝ)^4129 ≤ (16028603555271/50000000000000 : ℝ)^3105 := by
    have hnat : (2125333439 : ℕ)^4129*50000000000000^3105 ≤ 16028603555271^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125333439 5000000000 16028603555271 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187820651/5000000000 : ℝ), (4504362119/10000000000 : ℝ), (2125333439/5000000000 : ℝ)] ![(8329148999839/25000000000000 : ℝ), (34626196873281/100000000000000 : ℝ), (16028603555271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187820651/5000000000 : ℝ)|^4129 ≤ (8329148999839/25000000000000 : ℝ)^3105
        have hw : |(2187820651/5000000000 : ℝ)|=(2187820651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4504362119/10000000000 : ℝ)|^4129 ≤ (34626196873281/100000000000000 : ℝ)^3105
        have hw : |(4504362119/10000000000 : ℝ)|=(4504362119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2125333439/5000000000 : ℝ)|^4129 ≤ (16028603555271/50000000000000 : ℝ)^3105
        have hw : |(2125333439/5000000000 : ℝ)|=(2125333439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1065_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7007/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11239/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (703/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3501/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7007/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11239/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7007/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11239/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7007/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11239/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7007/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11239/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7007/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11239/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7007/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11239/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11239/100000 : ℝ) ^ (8257/2048 : ℝ) ≤ (14886150749582541/100000000000000000000 : ℝ) := by
    have hpowers : (11239/100000 : ℝ)^8257 ≤ (14886150749582541/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11239 : ℕ)^8257*100000000000000000000^2048 ≤ 14886150749582541^2048*100000^8257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11239 100000 14886150749582541 100000000000000000000 8257 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11239/100000 : ℝ)) (X := (14886150749582541/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7007/50000 : ℝ) ^ (8257/2048 : ℝ) ≤ (3623779809747229/10000000000000000000 : ℝ) := by
    have hpowers : (7007/50000 : ℝ)^8257 ≤ (3623779809747229/10000000000000000000 : ℝ)^2048 := by
      have hnat : (7007 : ℕ)^8257*10000000000000000000^2048 ≤ 3623779809747229^2048*50000^8257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7007 50000 3623779809747229 10000000000000000000 8257 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7007/50000 : ℝ)) (X := (3623779809747229/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014886150749582541/50000000000000000000 : ℝ) ≤ (2500184591405229/2500000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (50014886150749582541/50000000000000000000 : ℝ)^2048 ≤ (2500184591405229/2500000000000000 : ℝ)^8257 := by
      have hnat : (50014886150749582541 : ℕ)^2048*2500000000000000^8257 ≤ 2500184591405229^8257*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014886150749582541 50000000000000000000 2500184591405229 2500000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500184591405229/2500000000000000 : ℝ)) (X := (50014886150749582541/50000000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051123948847054831/100000000000000000000 : ℝ) ≤ (2000253558744529/2000000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (100051123948847054831/100000000000000000000 : ℝ)^2048 ≤ (2000253558744529/2000000000000000 : ℝ)^8257 := by
      have hnat : (100051123948847054831 : ℕ)^2048*2000000000000000^8257 ≤ 2000253558744529^8257*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051123948847054831 100000000000000000000 2000253558744529 2000000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000253558744529/2000000000000000 : ℝ)) (X := (100051123948847054831/100000000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003623779809747229/5000000000000000000 : ℝ) ≤ (5000898610912187/5000000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (5003623779809747229/5000000000000000000 : ℝ)^2048 ≤ (5000898610912187/5000000000000000 : ℝ)^8257 := by
      have hnat : (5003623779809747229 : ℕ)^2048*5000000000000000^8257 ≤ 5000898610912187^8257*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003623779809747229 5000000000000000000 5000898610912187 5000000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000898610912187/5000000000000000 : ℝ)) (X := (5003623779809747229/5000000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14886150749582541/100000000000000000000 : ℝ) ≤ ((13870074239863688719/13875000000000000000 : ℝ)+2*(529428101729/277500000000000 : ℝ)*(11239/100000 : ℝ))^(8257/2048 : ℝ) := by
    rw [show (13870074239863688719/13875000000000000000 : ℝ)+2*(529428101729/277500000000000 : ℝ)*(11239/100000 : ℝ)=(2500184591405229/2500000000000000 : ℝ) by norm_num, show 1+2*(14886150749582541/100000000000000000000 : ℝ)=(50014886150749582541/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3623779809747229/10000000000000000000 : ℝ)+(14886150749582541/100000000000000000000 : ℝ) ≤ ((13870074239863688719/13875000000000000000 : ℝ)+(529428101729/277500000000000 : ℝ)*((7007/50000 : ℝ)+(11239/100000 : ℝ)))^(8257/2048 : ℝ) := by
    rw [show (13870074239863688719/13875000000000000000 : ℝ)+(529428101729/277500000000000 : ℝ)*((7007/50000 : ℝ)+(11239/100000 : ℝ))=(2000253558744529/2000000000000000 : ℝ) by norm_num, show 1+(3623779809747229/10000000000000000000 : ℝ)+(14886150749582541/100000000000000000000 : ℝ)=(100051123948847054831/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3623779809747229/10000000000000000000 : ℝ) ≤ ((13870074239863688719/13875000000000000000 : ℝ)+2*(529428101729/277500000000000 : ℝ)*(7007/50000 : ℝ))^(8257/2048 : ℝ) := by
    rw [show (13870074239863688719/13875000000000000000 : ℝ)+2*(529428101729/277500000000000 : ℝ)*(7007/50000 : ℝ)=(5000898610912187/5000000000000000 : ℝ) by norm_num, show 1+2*(3623779809747229/10000000000000000000 : ℝ)=(5003623779809747229/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13870074239863688719/13875000000000000000 : ℝ)*(X 1 0+X 2 0)+(529428101729/277500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (11239/100000 : ℝ)) (hi := (7007/50000 : ℝ)) (c := (13870074239863688719/13875000000000000000 : ℝ)) (alpha := (529428101729/277500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13870074239863688719/13875000000000000000 : ℝ)*(X 0 1+X 2 1)+(529428101729/277500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (11239/100000 : ℝ)) (hi := (7007/50000 : ℝ)) (c := (13870074239863688719/13875000000000000000 : ℝ)) (alpha := (529428101729/277500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13870074239863688719/13875000000000000000 : ℝ)*(X 0 2+X 1 2)+(529428101729/277500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (11239/100000 : ℝ)) (hi := (7007/50000 : ℝ)) (c := (13870074239863688719/13875000000000000000 : ℝ)) (alpha := (529428101729/277500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-275531491/1250000000 : ℝ)*X 0 0+(1078894019/2000000000 : ℝ)*X 0 1+(5264344727/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345005461/10000000000 : ℝ)*X 1 0+(-1135137407/5000000000 : ℝ)*X 1 1+(5264344923/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((267250277/500000000 : ℝ)*X 2 0+(5264344767/10000000000 : ℝ)*X 2 1+(-1135137457/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((136738479/312500000 : ℝ)*X 0 0+(2125012547/5000000000 : ℝ)*X 0 1+(2252500799/5000000000 : ℝ)*X 0 2+(136738479/312500000 : ℝ)*X 1 0+(2125012547/5000000000 : ℝ)*X 1 1+(2252500799/5000000000 : ℝ)*X 1 2+(136738479/312500000 : ℝ)*X 2 0+(2125012547/5000000000 : ℝ)*X 2 1+(2252500799/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2204256917/10000000000 : ℝ)*X 0 0+(5264671237/10000000000 : ℝ)*X 0 1+(2697071241/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531223207/1000000000 : ℝ)*X 1 0+(-428095453/2000000000 : ℝ)*X 1 1+(2697071241/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531223207/1000000000 : ℝ)*X 2 0+(2697071241/5000000000 : ℝ)*X 2 1+(-428095453/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2187820651/5000000000 : ℝ)*X 0 0+(4504362119/10000000000 : ℝ)*X 0 1+(2125333439/5000000000 : ℝ)*X 0 2+(2187820651/5000000000 : ℝ)*X 1 0+(4504362119/10000000000 : ℝ)*X 1 1+(2125333439/5000000000 : ℝ)*X 1 2+(2187820651/5000000000 : ℝ)*X 2 0+(4504362119/10000000000 : ℝ)*X 2 1+(2125333439/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (98330428661067484948868873/14453125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1608775781/100000000000000 : ℝ)*(base19) + (1671868657/100000000000000 : ℝ)*(base23) + (262930099/100000000000000 : ℝ)*(upper3) + (26988333/100000000000000 : ℝ)*(upper4) + (719481/800000000000 : ℝ)*(upper5) + (362718128545879/6250000000000 : ℝ)*(major0) + (362718128545879/6250000000000 : ℝ)*(major1) + (362718128545879/6250000000000 : ℝ)*(major2) + (1921238196042259/25000000000000 : ℝ)*(sp0) + (3842500609572967/50000000000000 : ℝ)*(sp1) + (7685001156053059/100000000000000 : ℝ)*(sp2) + (980487824437937/25000000000000 : ℝ)*(sp3) + (50043752679/100000000000000 : ℝ)*(sp4) + (161006341/625000000000 : ℝ)*(sp7) + (980494264691577/25000000000000 : ℝ)*(f.failure) + (1921250706980429/25000000000000 : ℝ)*(f.sum) + (19193044883719/13875000000000000000000000000 : ℝ)*base66 + (815407913130007751/86718750000000000000000000000000 : ℝ)*base67 + (1101828658888601501/86718750000000000000000000000000 : ℝ)*base69 + (1704650181510476501/86718750000000000000000000000000 : ℝ)*base71 + (16703442258211/3468750000000000000000000000 : ℝ)*base74 + (251073440019851501/86718750000000000000000000000000 : ℝ)*base75 + (1713061788740164001/86718750000000000000000000000000 : ℝ)*base77 + (634618032190304749/86718750000000000000000000000000 : ℝ)*base80 + (5735031166547/6937500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (6401291/500000000000000000000 : ℝ)*base90 + (6401291/500000000000000000000 : ℝ)*base92 + (6401291/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (64695854438370580538135833/23125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (65871289/12500000000000 : ℝ)*(base19) + (286931059/50000000000000 : ℝ)*(base23) + (28436043/50000000000000 : ℝ)*(upper3) + (21314453/100000000000000 : ℝ)*(lower4) + (28877797/50000000000000 : ℝ)*(upper5) + (583272973078069/10000000000000 : ℝ)*(major0) + (583272973078069/10000000000000 : ℝ)*(major1) + (583272973078069/10000000000000 : ℝ)*(major2) + (3579476579/25000000000000 : ℝ)*(sp1) + (15414967291/100000000000000 : ℝ)*(sp2) + (3861861123125513/50000000000000 : ℝ)*(sp4) + (3861853700687199/50000000000000 : ℝ)*(sp5) + (7723706257421617/100000000000000 : ℝ)*(sp6) + (788347424411011/20000000000000 : ℝ)*(sp7) + (788347424411011/20000000000000 : ℝ)*(f.failure) + (3861861123125513/50000000000000 : ℝ)*(f.sum) + (5883094859299/1387500000000000000000000000 : ℝ)*base66 + (2458773444129596389/138750000000000000000000000000000 : ℝ)*base68 + (2311803077585846389/138750000000000000000000000000000 : ℝ)*base70 + (1972706725040846389/138750000000000000000000000000000 : ℝ)*base72 + (10875525948923/2775000000000000000000000000 : ℝ)*base74 + (5569725639950846389/138750000000000000000000000000000 : ℝ)*base76 + (2030081763958346389/138750000000000000000000000000000 : ℝ)*base78 + (1936089766153346389/138750000000000000000000000000000 : ℝ)*base80 + (6026949212077/2775000000000000000000000000 : ℝ)*base81 + (2228887/400000000000000000000 : ℝ)*base89 + (2228887/400000000000000000000 : ℝ)*base91 + (2228887/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1065_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7007/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11239/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (703/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3501/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1065_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1065_s8_0 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2204262659/10000000000 : ℝ)*x 0 + (1078873471/2000000000 : ℝ)*x 1 + (1316110061/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2204262659/10000000000 : ℝ)^4129 ≤ (13386829377553/100000000000000 : ℝ)^3105 := by
    have hnat : (2204262659 : ℕ)^4129*100000000000000^3105 ≤ 13386829377553^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2204262659 10000000000 13386829377553 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078873471/2000000000 : ℝ)^4129 ≤ (44008544473957/100000000000000 : ℝ)^3105 := by
    have hnat : (1078873471 : ℕ)^4129*100000000000000^3105 ≤ 44008544473957^3105*2000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078873471 2000000000 44008544473957 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316110061/2500000000 : ℝ)^4129 ≤ (213023130679/500000000000 : ℝ)^3105 := by
    have hnat : (1316110061 : ℕ)^4129*500000000000^3105 ≤ 213023130679^3105*2500000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316110061 2500000000 213023130679 500000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2204262659/10000000000 : ℝ), (1078873471/2000000000 : ℝ), (1316110061/2500000000 : ℝ)] ![(13386829377553/100000000000000 : ℝ), (44008544473957/100000000000000 : ℝ), (213023130679/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2204262659/10000000000 : ℝ)|^4129 ≤ (13386829377553/100000000000000 : ℝ)^3105
        have hw : |(-2204262659/10000000000 : ℝ)|=(2204262659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078873471/2000000000 : ℝ)|^4129 ≤ (44008544473957/100000000000000 : ℝ)^3105
        have hw : |(1078873471/2000000000 : ℝ)|=(1078873471/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316110061/2500000000 : ℝ)|^4129 ≤ (213023130679/500000000000 : ℝ)^3105
        have hw : |(1316110061/2500000000 : ℝ)|=(1316110061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s8_1 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344979263/10000000000 : ℝ)*x 0 + (-2270183767/10000000000 : ℝ)*x 1 + (1052888049/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344979263/10000000000 : ℝ)^4129 ≤ (8694711177633/20000000000000 : ℝ)^3105 := by
    have hnat : (5344979263 : ℕ)^4129*20000000000000^3105 ≤ 8694711177633^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344979263 10000000000 8694711177633 20000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2270183767/10000000000 : ℝ)^4129 ≤ (139218179559/1000000000000 : ℝ)^3105 := by
    have hnat : (2270183767 : ℕ)^4129*1000000000000^3105 ≤ 139218179559^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270183767 10000000000 139218179559 1000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052888049/2000000000 : ℝ)^4129 ≤ (21302313073281/50000000000000 : ℝ)^3105 := by
    have hnat : (1052888049 : ℕ)^4129*50000000000000^3105 ≤ 21302313073281^3105*2000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052888049 2000000000 21302313073281 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344979263/10000000000 : ℝ), (-2270183767/10000000000 : ℝ), (1052888049/2000000000 : ℝ)] ![(8694711177633/20000000000000 : ℝ), (139218179559/1000000000000 : ℝ), (21302313073281/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344979263/10000000000 : ℝ)|^4129 ≤ (8694711177633/20000000000000 : ℝ)^3105
        have hw : |(5344979263/10000000000 : ℝ)|=(5344979263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2270183767/10000000000 : ℝ)|^4129 ≤ (139218179559/1000000000000 : ℝ)^3105
        have hw : |(-2270183767/10000000000 : ℝ)|=(2270183767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052888049/2000000000 : ℝ)|^4129 ≤ (21302313073281/50000000000000 : ℝ)^3105
        have hw : |(1052888049/2000000000 : ℝ)|=(1052888049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s8_2 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344979263/10000000000 : ℝ)*x 0 + (2632220123/5000000000 : ℝ)*x 1 + (-454036753/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344979263/10000000000 : ℝ)^4129 ≤ (8694711177633/20000000000000 : ℝ)^3105 := by
    have hnat : (5344979263 : ℕ)^4129*20000000000000^3105 ≤ 8694711177633^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344979263 10000000000 8694711177633 20000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632220123/5000000000 : ℝ)^4129 ≤ (10651156539331/25000000000000 : ℝ)^3105 := by
    have hnat : (2632220123 : ℕ)^4129*25000000000000^3105 ≤ 10651156539331^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632220123 5000000000 10651156539331 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (454036753/2000000000 : ℝ)^4129 ≤ (13921817939591/100000000000000 : ℝ)^3105 := by
    have hnat : (454036753 : ℕ)^4129*100000000000000^3105 ≤ 13921817939591^3105*2000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454036753 2000000000 13921817939591 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344979263/10000000000 : ℝ), (2632220123/5000000000 : ℝ), (-454036753/2000000000 : ℝ)] ![(8694711177633/20000000000000 : ℝ), (10651156539331/25000000000000 : ℝ), (13921817939591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344979263/10000000000 : ℝ)|^4129 ≤ (8694711177633/20000000000000 : ℝ)^3105
        have hw : |(5344979263/10000000000 : ℝ)|=(5344979263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632220123/5000000000 : ℝ)|^4129 ≤ (10651156539331/25000000000000 : ℝ)^3105
        have hw : |(2632220123/5000000000 : ℝ)|=(2632220123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-454036753/2000000000 : ℝ)|^4129 ≤ (13921817939591/100000000000000 : ℝ)^3105
        have hw : |(-454036753/2000000000 : ℝ)|=(454036753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s8_3 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (136738637/312500000 : ℝ)*x 0 + (2125109217/5000000000 : ℝ)*x 1 + (4504806927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (136738637/312500000 : ℝ)^4129 ≤ (6663309240759/20000000000000 : ℝ)^3105 := by
    have hnat : (136738637 : ℕ)^4129*20000000000000^3105 ≤ 6663309240759^3105*312500000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136738637 312500000 6663309240759 20000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2125109217/5000000000 : ℝ)^4129 ≤ (8013177450839/25000000000000 : ℝ)^3105 := by
    have hnat : (2125109217 : ℕ)^4129*25000000000000^3105 ≤ 8013177450839^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2125109217 5000000000 8013177450839 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4504806927/10000000000 : ℝ)^4129 ≤ (8657685993139/25000000000000 : ℝ)^3105 := by
    have hnat : (4504806927 : ℕ)^4129*25000000000000^3105 ≤ 8657685993139^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504806927 10000000000 8657685993139 25000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(136738637/312500000 : ℝ), (2125109217/5000000000 : ℝ), (4504806927/10000000000 : ℝ)] ![(6663309240759/20000000000000 : ℝ), (8013177450839/25000000000000 : ℝ), (8657685993139/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(136738637/312500000 : ℝ)|^4129 ≤ (6663309240759/20000000000000 : ℝ)^3105
        have hw : |(136738637/312500000 : ℝ)|=(136738637/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2125109217/5000000000 : ℝ)|^4129 ≤ (8013177450839/25000000000000 : ℝ)^3105
        have hw : |(2125109217/5000000000 : ℝ)|=(2125109217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4504806927/10000000000 : ℝ)|^4129 ≤ (8657685993139/25000000000000 : ℝ)^3105
        have hw : |(4504806927/10000000000 : ℝ)|=(4504806927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s8_4 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-275533469/1250000000 : ℝ)*x 0 + (105295309/200000000 : ℝ)*x 1 + (1078808191/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (275533469/1250000000 : ℝ)^4129 ≤ (2677374101753/20000000000000 : ℝ)^3105 := by
    have hnat : (275533469 : ℕ)^4129*20000000000000^3105 ≤ 2677374101753^3105*1250000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275533469 1250000000 2677374101753 20000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105295309/200000000 : ℝ)^4129 ≤ (4260812599691/10000000000000 : ℝ)^3105 := by
    have hnat : (105295309 : ℕ)^4129*10000000000000^3105 ≤ 4260812599691^3105*200000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105295309 200000000 4260812599691 10000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078808191/2000000000 : ℝ)^4129 ≤ (44005003476769/100000000000000 : ℝ)^3105 := by
    have hnat : (1078808191 : ℕ)^4129*100000000000000^3105 ≤ 44005003476769^3105*2000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078808191 2000000000 44005003476769 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-275533469/1250000000 : ℝ), (105295309/200000000 : ℝ), (1078808191/2000000000 : ℝ)] ![(2677374101753/20000000000000 : ℝ), (4260812599691/10000000000000 : ℝ), (44005003476769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-275533469/1250000000 : ℝ)|^4129 ≤ (2677374101753/20000000000000 : ℝ)^3105
        have hw : |(-275533469/1250000000 : ℝ)|=(275533469/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105295309/200000000 : ℝ)|^4129 ≤ (4260812599691/10000000000000 : ℝ)^3105
        have hw : |(105295309/200000000 : ℝ)|=(105295309/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078808191/2000000000 : ℝ)|^4129 ≤ (44005003476769/100000000000000 : ℝ)^3105
        have hw : |(1078808191/2000000000 : ℝ)|=(1078808191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s8_5 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312256199/10000000000 : ℝ)*x 0 + (-85623283/400000000 : ℝ)*x 1 + (5394041203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312256199/10000000000 : ℝ)^4129 ≤ (8623996897927/20000000000000 : ℝ)^3105 := by
    have hnat : (5312256199 : ℕ)^4129*20000000000000^3105 ≤ 8623996897927^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312256199 10000000000 8623996897927 20000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85623283/400000000 : ℝ)^4129 ≤ (6437504666323/50000000000000 : ℝ)^3105 := by
    have hnat : (85623283 : ℕ)^4129*50000000000000^3105 ≤ 6437504666323^3105*400000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85623283 400000000 6437504666323 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394041203/10000000000 : ℝ)^4129 ≤ (22002503083603/50000000000000 : ℝ)^3105 := by
    have hnat : (5394041203 : ℕ)^4129*50000000000000^3105 ≤ 22002503083603^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394041203 10000000000 22002503083603 50000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312256199/10000000000 : ℝ), (-85623283/400000000 : ℝ), (5394041203/10000000000 : ℝ)] ![(8623996897927/20000000000000 : ℝ), (6437504666323/50000000000000 : ℝ), (22002503083603/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312256199/10000000000 : ℝ)|^4129 ≤ (8623996897927/20000000000000 : ℝ)^3105
        have hw : |(5312256199/10000000000 : ℝ)|=(5312256199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-85623283/400000000 : ℝ)|^4129 ≤ (6437504666323/50000000000000 : ℝ)^3105
        have hw : |(-85623283/400000000 : ℝ)|=(85623283/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394041203/10000000000 : ℝ)|^4129 ≤ (22002503083603/50000000000000 : ℝ)^3105
        have hw : |(5394041203/10000000000 : ℝ)|=(5394041203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s8_6 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656127359/5000000000 : ℝ)*x 0 + (5394041103/10000000000 : ℝ)*x 1 + (-133786513/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656127359/5000000000 : ℝ)^4129 ≤ (8623993700741/20000000000000 : ℝ)^3105 := by
    have hnat : (2656127359 : ℕ)^4129*20000000000000^3105 ≤ 8623993700741^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656127359 5000000000 8623993700741 20000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394041103/10000000000 : ℝ)^4129 ≤ (2750312817647/6250000000000 : ℝ)^3105 := by
    have hnat : (5394041103 : ℕ)^4129*6250000000000^3105 ≤ 2750312817647^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394041103 10000000000 2750312817647 6250000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (133786513/625000000 : ℝ)^4129 ≤ (804689149567/6250000000000 : ℝ)^3105 := by
    have hnat : (133786513 : ℕ)^4129*6250000000000^3105 ≤ 804689149567^3105*625000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133786513 625000000 804689149567 6250000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656127359/5000000000 : ℝ), (5394041103/10000000000 : ℝ), (-133786513/625000000 : ℝ)] ![(8623993700741/20000000000000 : ℝ), (2750312817647/6250000000000 : ℝ), (804689149567/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656127359/5000000000 : ℝ)|^4129 ≤ (8623993700741/20000000000000 : ℝ)^3105
        have hw : |(2656127359/5000000000 : ℝ)|=(2656127359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394041103/10000000000 : ℝ)|^4129 ≤ (2750312817647/6250000000000 : ℝ)^3105
        have hw : |(5394041103/10000000000 : ℝ)|=(5394041103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-133786513/625000000 : ℝ)|^4129 ≤ (804689149567/6250000000000 : ℝ)^3105
        have hw : |(-133786513/625000000 : ℝ)|=(133786513/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1065_s8_7 (p : ℝ) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (875129033/2000000000 : ℝ)*x 0 + (2252084723/5000000000 : ℝ)*x 1 + (4250859367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (875129033/2000000000 : ℝ)^4129 ≤ (33316635112881/100000000000000 : ℝ)^3105 := by
    have hnat : (875129033 : ℕ)^4129*100000000000000^3105 ≤ 33316635112881^3105*2000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      875129033 2000000000 33316635112881 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252084723/5000000000 : ℝ)^4129 ≤ (34624227298063/100000000000000 : ℝ)^3105 := by
    have hnat : (2252084723 : ℕ)^4129*100000000000000^3105 ≤ 34624227298063^3105*5000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252084723 5000000000 34624227298063 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4250859367/10000000000 : ℝ)^4129 ≤ (32059137571619/100000000000000 : ℝ)^3105 := by
    have hnat : (4250859367 : ℕ)^4129*100000000000000^3105 ≤ 32059137571619^3105*10000000000^4129 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250859367 10000000000 32059137571619 100000000000000 4129 3105 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4129/1024 : ℝ)) 4129 3105 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(875129033/2000000000 : ℝ), (2252084723/5000000000 : ℝ), (4250859367/10000000000 : ℝ)] ![(33316635112881/100000000000000 : ℝ), (34624227298063/100000000000000 : ℝ), (32059137571619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(875129033/2000000000 : ℝ)|^4129 ≤ (33316635112881/100000000000000 : ℝ)^3105
        have hw : |(875129033/2000000000 : ℝ)|=(875129033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252084723/5000000000 : ℝ)|^4129 ≤ (34624227298063/100000000000000 : ℝ)^3105
        have hw : |(2252084723/5000000000 : ℝ)|=(2252084723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4250859367/10000000000 : ℝ)|^4129 ≤ (32059137571619/100000000000000 : ℝ)^3105
        have hw : |(4250859367/10000000000 : ℝ)|=(4250859367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1065_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3501/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (703/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (9/80 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7001/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3501/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (703/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3501/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (703/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3501/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (703/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3501/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (703/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3501/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (703/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3501/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (703/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
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
  have hpowlo : (703/6250 : ℝ) ^ (8257/2048 : ℝ) ≤ (14934269764888703/100000000000000000000 : ℝ) := by
    have hpowers : (703/6250 : ℝ)^8257 ≤ (14934269764888703/100000000000000000000 : ℝ)^2048 := by
      have hnat : (703 : ℕ)^8257*100000000000000000000^2048 ≤ 14934269764888703^2048*6250^8257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        703 6250 14934269764888703 100000000000000000000 8257 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (703/6250 : ℝ)) (X := (14934269764888703/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3501/25000 : ℝ) ^ (8257/2048 : ℝ) ≤ (36133656982150293/100000000000000000000 : ℝ) := by
    have hpowers : (3501/25000 : ℝ)^8257 ≤ (36133656982150293/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3501 : ℕ)^8257*100000000000000000000^2048 ≤ 36133656982150293^2048*25000^8257 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3501 25000 36133656982150293 100000000000000000000 8257 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3501/25000 : ℝ)) (X := (36133656982150293/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014934269764888703/50000000000000000000 : ℝ) ≤ (2500185188024163/2500000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (50014934269764888703/50000000000000000000 : ℝ)^2048 ≤ (2500185188024163/2500000000000000 : ℝ)^8257 := by
      have hnat : (50014934269764888703 : ℕ)^2048*2500000000000000^8257 ≤ 2500185188024163^8257*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014934269764888703 50000000000000000000 2500185188024163 2500000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500185188024163/2500000000000000 : ℝ)) (X := (50014934269764888703/50000000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012766981686759749/25000000000000000000 : ℝ) ≤ (5000633202364549/5000000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (25012766981686759749/25000000000000000000 : ℝ)^2048 ≤ (5000633202364549/5000000000000000 : ℝ)^8257 := by
      have hnat : (25012766981686759749 : ℕ)^2048*5000000000000000^8257 ≤ 5000633202364549^8257*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012766981686759749 25000000000000000000 5000633202364549 5000000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000633202364549/5000000000000000 : ℝ)) (X := (25012766981686759749/25000000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036133656982150293/50000000000000000000 : ℝ) ≤ (1250224007170193/1250000000000000 : ℝ) ^ (8257/2048 : ℝ) := by
    have hpowers : (50036133656982150293/50000000000000000000 : ℝ)^2048 ≤ (1250224007170193/1250000000000000 : ℝ)^8257 := by
      have hnat : (50036133656982150293 : ℕ)^2048*1250000000000000^8257 ≤ 1250224007170193^8257*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036133656982150293 50000000000000000000 1250224007170193 1250000000000000 2048 8257 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250224007170193/1250000000000000 : ℝ)) (X := (50036133656982150293/50000000000000000000 : ℝ)) (by norm_num) 8257 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14934269764888703/100000000000000000000 : ℝ) ≤ ((1721888526947429231/1722500000000000000 : ℝ)+2*(262826316223/137800000000000 : ℝ)*(703/6250 : ℝ))^(8257/2048 : ℝ) := by
    rw [show (1721888526947429231/1722500000000000000 : ℝ)+2*(262826316223/137800000000000 : ℝ)*(703/6250 : ℝ)=(2500185188024163/2500000000000000 : ℝ) by norm_num, show 1+2*(14934269764888703/100000000000000000000 : ℝ)=(50014934269764888703/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36133656982150293/100000000000000000000 : ℝ)+(14934269764888703/100000000000000000000 : ℝ) ≤ ((1721888526947429231/1722500000000000000 : ℝ)+(262826316223/137800000000000 : ℝ)*((3501/25000 : ℝ)+(703/6250 : ℝ)))^(8257/2048 : ℝ) := by
    rw [show (1721888526947429231/1722500000000000000 : ℝ)+(262826316223/137800000000000 : ℝ)*((3501/25000 : ℝ)+(703/6250 : ℝ))=(5000633202364549/5000000000000000 : ℝ) by norm_num, show 1+(36133656982150293/100000000000000000000 : ℝ)+(14934269764888703/100000000000000000000 : ℝ)=(25012766981686759749/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36133656982150293/100000000000000000000 : ℝ) ≤ ((1721888526947429231/1722500000000000000 : ℝ)+2*(262826316223/137800000000000 : ℝ)*(3501/25000 : ℝ))^(8257/2048 : ℝ) := by
    rw [show (1721888526947429231/1722500000000000000 : ℝ)+2*(262826316223/137800000000000 : ℝ)*(3501/25000 : ℝ)=(1250224007170193/1250000000000000 : ℝ) by norm_num, show 1+2*(36133656982150293/100000000000000000000 : ℝ)=(50036133656982150293/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1721888526947429231/1722500000000000000 : ℝ)*(X 1 0+X 2 0)+(262826316223/137800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (703/6250 : ℝ)) (hi := (3501/25000 : ℝ)) (c := (1721888526947429231/1722500000000000000 : ℝ)) (alpha := (262826316223/137800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1721888526947429231/1722500000000000000 : ℝ)*(X 0 1+X 2 1)+(262826316223/137800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (703/6250 : ℝ)) (hi := (3501/25000 : ℝ)) (c := (1721888526947429231/1722500000000000000 : ℝ)) (alpha := (262826316223/137800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1721888526947429231/1722500000000000000 : ℝ)*(X 0 2+X 1 2)+(262826316223/137800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8257/2048 : ℝ)) (lo := (703/6250 : ℝ)) (hi := (3501/25000 : ℝ)) (c := (1721888526947429231/1722500000000000000 : ℝ)) (alpha := (262826316223/137800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2204262659/10000000000 : ℝ)*X 0 0+(1078873471/2000000000 : ℝ)*X 0 1+(1316110061/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344979263/10000000000 : ℝ)*X 1 0+(-2270183767/10000000000 : ℝ)*X 1 1+(1052888049/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344979263/10000000000 : ℝ)*X 2 0+(2632220123/5000000000 : ℝ)*X 2 1+(-454036753/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((136738637/312500000 : ℝ)*X 0 0+(2125109217/5000000000 : ℝ)*X 0 1+(4504806927/10000000000 : ℝ)*X 0 2+(136738637/312500000 : ℝ)*X 1 0+(2125109217/5000000000 : ℝ)*X 1 1+(4504806927/10000000000 : ℝ)*X 1 2+(136738637/312500000 : ℝ)*X 2 0+(2125109217/5000000000 : ℝ)*X 2 1+(4504806927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-275533469/1250000000 : ℝ)*X 0 0+(105295309/200000000 : ℝ)*X 0 1+(1078808191/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312256199/10000000000 : ℝ)*X 1 0+(-85623283/400000000 : ℝ)*X 1 1+(5394041203/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656127359/5000000000 : ℝ)*X 2 0+(5394041103/10000000000 : ℝ)*X 2 1+(-133786513/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((875129033/2000000000 : ℝ)*X 0 0+(2252084723/5000000000 : ℝ)*X 0 1+(4250859367/10000000000 : ℝ)*X 0 2+(875129033/2000000000 : ℝ)*X 1 0+(2252084723/5000000000 : ℝ)*X 1 1+(4250859367/10000000000 : ℝ)*X 1 2+(875129033/2000000000 : ℝ)*X 2 0+(2252084723/5000000000 : ℝ)*X 2 1+(4250859367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1065_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16931990315130890969739693/2153125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (63009237/4000000000000 : ℝ)*(base19) + (366821489/25000000000000 : ℝ)*(base23) + (57696363/100000000000000 : ℝ)*(lower2) + (197810607/100000000000000 : ℝ)*(upper3) + (120103763/100000000000000 : ℝ)*(upper5) + (72654134390219/1250000000000 : ℝ)*(major0) + (72654134390219/1250000000000 : ℝ)*(major1) + (72654134390219/1250000000000 : ℝ)*(major2) + (769666731835603/10000000000000 : ℝ)*(sp0) + (76967080977601/1000000000000 : ℝ)*(sp1) + (7696708205705069/100000000000000 : ℝ)*(sp2) + (1963964149930149/50000000000000 : ℝ)*(sp3) + (8470926999/20000000000000 : ℝ)*(sp4) + (23267453233/100000000000000 : ℝ)*(sp7) + (981987891828383/25000000000000 : ℝ)*(f.failure) + (307868386919641/4000000000000 : ℝ)*(f.sum) + (2167460820333/689000000000000000000000000 : ℝ)*base65 + (17807010055147839/2153125000000000000000000000000 : ℝ)*base67 + (16331828183064661/2153125000000000000000000000000 : ℝ)*base70 + (7951314105043509/538281250000000000000000000000 : ℝ)*base72 + (2828185504373/344500000000000000000000000 : ℝ)*base73 + (5932993612949759/538281250000000000000000000000 : ℝ)*base76 + (12104545596995911/2153125000000000000000000000000 : ℝ)*base78 + (9136084265120911/2153125000000000000000000000000 : ℝ)*base80 + (111457876253/172250000000000000000000000 : ℝ)*base82 + (7452611/500000000000000000000 : ℝ)*base89 + (7452611/500000000000000000000 : ℝ)*base91 + (7452611/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (555272671527437062032291741/86125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (135990091/100000000000000 : ℝ)*(base8) + (282047079/100000000000000 : ℝ)*(upper1) + (957910889/100000000000000 : ℝ)*(upper2) + (6275787/25000000000000 : ℝ)*(upper3) + (426032773/100000000000000 : ℝ)*(lower4) + (5841575483113421/100000000000000 : ℝ)*(major0) + (5841575483113421/100000000000000 : ℝ)*(major1) + (5841575483113421/100000000000000 : ℝ)*(major2) + (1301725967/4000000000000 : ℝ)*(sp0) + (9103885977/12500000000000 : ℝ)*(sp1) + (3867701511749957/50000000000000 : ℝ)*(sp4) + (1933840717887841/25000000000000 : ℝ)*(sp5) + (386771785131959/5000000000000 : ℝ)*(sp6) + (197385752433903/5000000000000 : ℝ)*(sp7) + (197385752433903/5000000000000 : ℝ)*(f.failure) + (386771785131959/5000000000000 : ℝ)*(f.sum) + (10760379127053/6890000000000000000000000000 : ℝ)*base65 + (67294429688596751/172250000000000000000000000000000 : ℝ)*base67 + (866352463927346751/172250000000000000000000000000000 : ℝ)*base69 + (255264522950846751/172250000000000000000000000000000 : ℝ)*base71 + (18124264087563/6890000000000000000000000000 : ℝ)*base73 + (400238926992846751/172250000000000000000000000000000 : ℝ)*base75 + (841123600689846751/172250000000000000000000000000000 : ℝ)*base77 + (295032680379846751/172250000000000000000000000000000 : ℝ)*base79 + (23631806312683/6890000000000000000000000000 : ℝ)*base81 + (509549/100000000000000000000 : ℝ)*base90 + (509549/100000000000000000000 : ℝ)*base92 + (509549/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1065_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3501/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (703/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9/80 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7001/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1065_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1065_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11197/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9/80 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7001/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1065_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1065_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1065_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8257/2048 : ℝ) ≤ p) (hpb : p ≤ (4129/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29594717/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7029/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11197/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9/80 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7001/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1065_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
