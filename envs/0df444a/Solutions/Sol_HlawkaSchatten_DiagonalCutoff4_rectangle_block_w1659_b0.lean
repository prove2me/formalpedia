-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1659_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:18:18.215993+00:00
-- url     : https://prove2.me/submissions/799f3663-51f2-4d83-bf99-1452fcc2dec1

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
theorem support_rectangle_w1659_s0_0 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-92312111/625000000 : ℝ)*x 0 + (5774257583/10000000000 : ℝ)*x 1 + (4927606309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (92312111/625000000 : ℝ)^4955 ≤ (4487218318891/50000000000000 : ℝ)^3931 := by
    have hnat : (92312111 : ℕ)^4955*50000000000000^3931 ≤ 4487218318891^3931*625000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92312111 625000000 4487218318891 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5774257583/10000000000 : ℝ)^4955 ≤ (50045778388927/100000000000000 : ℝ)^3931 := by
    have hnat : (5774257583 : ℕ)^4955*100000000000000^3931 ≤ 50045778388927^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5774257583 10000000000 50045778388927 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4927606309/10000000000 : ℝ)^4955 ≤ (40979784958411/100000000000000 : ℝ)^3931 := by
    have hnat : (4927606309 : ℕ)^4955*100000000000000^3931 ≤ 40979784958411^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4927606309 10000000000 40979784958411 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-92312111/625000000 : ℝ), (5774257583/10000000000 : ℝ), (4927606309/10000000000 : ℝ)] ![(4487218318891/50000000000000 : ℝ), (50045778388927/100000000000000 : ℝ), (40979784958411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-92312111/625000000 : ℝ)|^4955 ≤ (4487218318891/50000000000000 : ℝ)^3931
        have hw : |(-92312111/625000000 : ℝ)|=(92312111/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5774257583/10000000000 : ℝ)|^4955 ≤ (50045778388927/100000000000000 : ℝ)^3931
        have hw : |(5774257583/10000000000 : ℝ)|=(5774257583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4927606309/10000000000 : ℝ)|^4955 ≤ (40979784958411/100000000000000 : ℝ)^3931
        have hw : |(4927606309/10000000000 : ℝ)|=(4927606309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s0_1 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2716992329/5000000000 : ℝ)*x 0 + (-970449339/5000000000 : ℝ)*x 1 + (4927606937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2716992329/5000000000 : ℝ)^4955 ≤ (11589334023431/25000000000000 : ℝ)^3931 := by
    have hnat : (2716992329 : ℕ)^4955*25000000000000^3931 ≤ 11589334023431^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716992329 5000000000 11589334023431 25000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (970449339/5000000000 : ℝ)^4955 ≤ (12662872352343/100000000000000 : ℝ)^3931 := by
    have hnat : (970449339 : ℕ)^4955*100000000000000^3931 ≤ 12662872352343^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970449339 5000000000 12662872352343 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4927606937/10000000000 : ℝ)^4955 ≤ (10244947885391/25000000000000 : ℝ)^3931 := by
    have hnat : (4927606937 : ℕ)^4955*25000000000000^3931 ≤ 10244947885391^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4927606937 10000000000 10244947885391 25000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2716992329/5000000000 : ℝ), (-970449339/5000000000 : ℝ), (4927606937/10000000000 : ℝ)] ![(11589334023431/25000000000000 : ℝ), (12662872352343/100000000000000 : ℝ), (10244947885391/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2716992329/5000000000 : ℝ)|^4955 ≤ (11589334023431/25000000000000 : ℝ)^3931
        have hw : |(2716992329/5000000000 : ℝ)|=(2716992329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-970449339/5000000000 : ℝ)|^4955 ≤ (12662872352343/100000000000000 : ℝ)^3931
        have hw : |(-970449339/5000000000 : ℝ)|=(970449339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4927606937/10000000000 : ℝ)|^4955 ≤ (10244947885391/25000000000000 : ℝ)^3931
        have hw : |(4927606937/10000000000 : ℝ)|=(4927606937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s0_2 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2716992973/5000000000 : ℝ)*x 0 + (985521207/2000000000 : ℝ)*x 1 + (-60653067/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2716992973/5000000000 : ℝ)^4955 ≤ (2317867497197/5000000000000 : ℝ)^3931 := by
    have hnat : (2716992973 : ℕ)^4955*5000000000000^3931 ≤ 2317867497197^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716992973 5000000000 2317867497197 5000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (985521207/2000000000 : ℝ)^4955 ≤ (80038636887/195312500000 : ℝ)^3931 := by
    have hnat : (985521207 : ℕ)^4955*195312500000^3931 ≤ 80038636887^3931*2000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      985521207 2000000000 80038636887 195312500000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (60653067/312500000 : ℝ)^4955 ≤ (633143398043/5000000000000 : ℝ)^3931 := by
    have hnat : (60653067 : ℕ)^4955*5000000000000^3931 ≤ 633143398043^3931*312500000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60653067 312500000 633143398043 5000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2716992973/5000000000 : ℝ), (985521207/2000000000 : ℝ), (-60653067/312500000 : ℝ)] ![(2317867497197/5000000000000 : ℝ), (80038636887/195312500000 : ℝ), (633143398043/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2716992973/5000000000 : ℝ)|^4955 ≤ (2317867497197/5000000000000 : ℝ)^3931
        have hw : |(2716992973/5000000000 : ℝ)|=(2716992973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(985521207/2000000000 : ℝ)|^4955 ≤ (80038636887/195312500000 : ℝ)^3931
        have hw : |(985521207/2000000000 : ℝ)|=(985521207/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-60653067/312500000 : ℝ)|^4955 ≤ (633143398043/5000000000000 : ℝ)^3931
        have hw : |(-60653067/312500000 : ℝ)|=(60653067/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s0_3 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2043211469/5000000000 : ℝ)*x 0 + (616985059/2000000000 : ℝ)*x 1 + (1325070251/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2043211469/5000000000 : ℝ)^4955 ≤ (3236687478443/10000000000000 : ℝ)^3931 := by
    have hnat : (2043211469 : ℕ)^4955*10000000000000^3931 ≤ 3236687478443^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043211469 5000000000 3236687478443 10000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (616985059/2000000000 : ℝ)^4955 ≤ (5677226289417/25000000000000 : ℝ)^3931 := by
    have hnat : (616985059 : ℕ)^4955*25000000000000^3931 ≤ 5677226289417^3931*2000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      616985059 2000000000 5677226289417 25000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1325070251/2500000000 : ℝ)^4955 ≤ (44924220037923/100000000000000 : ℝ)^3931 := by
    have hnat : (1325070251 : ℕ)^4955*100000000000000^3931 ≤ 44924220037923^3931*2500000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325070251 2500000000 44924220037923 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2043211469/5000000000 : ℝ), (616985059/2000000000 : ℝ), (1325070251/2500000000 : ℝ)] ![(3236687478443/10000000000000 : ℝ), (5677226289417/25000000000000 : ℝ), (44924220037923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2043211469/5000000000 : ℝ)|^4955 ≤ (3236687478443/10000000000000 : ℝ)^3931
        have hw : |(2043211469/5000000000 : ℝ)|=(2043211469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(616985059/2000000000 : ℝ)|^4955 ≤ (5677226289417/25000000000000 : ℝ)^3931
        have hw : |(616985059/2000000000 : ℝ)|=(616985059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1325070251/2500000000 : ℝ)|^4955 ≤ (44924220037923/100000000000000 : ℝ)^3931
        have hw : |(1325070251/2500000000 : ℝ)|=(1325070251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s0_4 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-739595421/5000000000 : ℝ)*x 0 + (4948505267/10000000000 : ℝ)*x 1 + (2876321017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (739595421/5000000000 : ℝ)^4955 ≤ (449563355599/5000000000000 : ℝ)^3931 := by
    have hnat : (739595421 : ℕ)^4955*5000000000000^3931 ≤ 449563355599^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      739595421 5000000000 449563355599 5000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4948505267/10000000000 : ℝ)^4955 ≤ (10299745982161/25000000000000 : ℝ)^3931 := by
    have hnat : (4948505267 : ℕ)^4955*25000000000000^3931 ≤ 10299745982161^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4948505267 10000000000 10299745982161 25000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2876321017/5000000000 : ℝ)^4955 ≤ (1556554654517/3125000000000 : ℝ)^3931 := by
    have hnat : (2876321017 : ℕ)^4955*3125000000000^3931 ≤ 1556554654517^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2876321017 5000000000 1556554654517 3125000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-739595421/5000000000 : ℝ), (4948505267/10000000000 : ℝ), (2876321017/5000000000 : ℝ)] ![(449563355599/5000000000000 : ℝ), (10299745982161/25000000000000 : ℝ), (1556554654517/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-739595421/5000000000 : ℝ)|^4955 ≤ (449563355599/5000000000000 : ℝ)^3931
        have hw : |(-739595421/5000000000 : ℝ)|=(739595421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4948505267/10000000000 : ℝ)|^4955 ≤ (10299745982161/25000000000000 : ℝ)^3931
        have hw : |(4948505267/10000000000 : ℝ)|=(4948505267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2876321017/5000000000 : ℝ)|^4955 ≤ (1556554654517/3125000000000 : ℝ)^3931
        have hw : |(2876321017/5000000000 : ℝ)|=(2876321017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s0_5 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1040604931/2000000000 : ℝ)*x 0 + (-1115864879/10000000000 : ℝ)*x 1 + (2876320233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1040604931/2000000000 : ℝ)^4955 ≤ (43887655597419/100000000000000 : ℝ)^3931 := by
    have hnat : (1040604931 : ℕ)^4955*100000000000000^3931 ≤ 43887655597419^3931*2000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040604931 2000000000 43887655597419 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1115864879/10000000000 : ℝ)^4955 ≤ (63026125633/1000000000000 : ℝ)^3931 := by
    have hnat : (1115864879 : ℕ)^4955*1000000000000^3931 ≤ 63026125633^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115864879 10000000000 63026125633 1000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2876320233/5000000000 : ℝ)^4955 ≤ (3113108239453/6250000000000 : ℝ)^3931 := by
    have hnat : (2876320233 : ℕ)^4955*6250000000000^3931 ≤ 3113108239453^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2876320233 5000000000 3113108239453 6250000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1040604931/2000000000 : ℝ), (-1115864879/10000000000 : ℝ), (2876320233/5000000000 : ℝ)] ![(43887655597419/100000000000000 : ℝ), (63026125633/1000000000000 : ℝ), (3113108239453/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1040604931/2000000000 : ℝ)|^4955 ≤ (43887655597419/100000000000000 : ℝ)^3931
        have hw : |(1040604931/2000000000 : ℝ)|=(1040604931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1115864879/10000000000 : ℝ)|^4955 ≤ (63026125633/1000000000000 : ℝ)^3931
        have hw : |(-1115864879/10000000000 : ℝ)|=(1115864879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2876320233/5000000000 : ℝ)|^4955 ≤ (3113108239453/6250000000000 : ℝ)^3931
        have hw : |(2876320233/5000000000 : ℝ)|=(2876320233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s0_6 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5203023693/10000000000 : ℝ)*x 0 + (71908021/125000000 : ℝ)*x 1 + (-557932227/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5203023693/10000000000 : ℝ)^4955 ≤ (43887645369149/100000000000000 : ℝ)^3931 := by
    have hnat : (5203023693 : ℕ)^4955*100000000000000^3931 ≤ 43887645369149^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5203023693 10000000000 43887645369149 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (71908021/125000000 : ℝ)^4955 ≤ (9961949016191/20000000000000 : ℝ)^3931 := by
    have hnat : (71908021 : ℕ)^4955*20000000000000^3931 ≤ 9961949016191^3931*125000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71908021 125000000 9961949016191 20000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (557932227/5000000000 : ℝ)^4955 ≤ (787826192189/12500000000000 : ℝ)^3931 := by
    have hnat : (557932227 : ℕ)^4955*12500000000000^3931 ≤ 787826192189^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557932227 5000000000 787826192189 12500000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5203023693/10000000000 : ℝ), (71908021/125000000 : ℝ), (-557932227/5000000000 : ℝ)] ![(43887645369149/100000000000000 : ℝ), (9961949016191/20000000000000 : ℝ), (787826192189/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5203023693/10000000000 : ℝ)|^4955 ≤ (43887645369149/100000000000000 : ℝ)^3931
        have hw : |(5203023693/10000000000 : ℝ)|=(5203023693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(71908021/125000000 : ℝ)|^4955 ≤ (9961949016191/20000000000000 : ℝ)^3931
        have hw : |(71908021/125000000 : ℝ)|=(71908021/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-557932227/5000000000 : ℝ)|^4955 ≤ (787826192189/12500000000000 : ℝ)^3931
        have hw : |(-557932227/5000000000 : ℝ)|=(557932227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s0_7 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4092168373/10000000000 : ℝ)*x 0 + (2622798109/5000000000 : ℝ)*x 1 + (1570743747/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4092168373/10000000000 : ℝ)^4955 ≤ (506628857019/1562500000000 : ℝ)^3931 := by
    have hnat : (4092168373 : ℕ)^4955*1562500000000^3931 ≤ 506628857019^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4092168373 10000000000 506628857019 1562500000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622798109/5000000000 : ℝ)^4955 ≤ (22170385255317/50000000000000 : ℝ)^3931 := by
    have hnat : (2622798109 : ℕ)^4955*50000000000000^3931 ≤ 22170385255317^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622798109 5000000000 22170385255317 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1570743747/5000000000 : ℝ)^4955 ≤ (1161749131133/5000000000000 : ℝ)^3931 := by
    have hnat : (1570743747 : ℕ)^4955*5000000000000^3931 ≤ 1161749131133^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1570743747 5000000000 1161749131133 5000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4092168373/10000000000 : ℝ), (2622798109/5000000000 : ℝ), (1570743747/5000000000 : ℝ)] ![(506628857019/1562500000000 : ℝ), (22170385255317/50000000000000 : ℝ), (1161749131133/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4092168373/10000000000 : ℝ)|^4955 ≤ (506628857019/1562500000000 : ℝ)^3931
        have hw : |(4092168373/10000000000 : ℝ)|=(4092168373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622798109/5000000000 : ℝ)|^4955 ≤ (22170385255317/50000000000000 : ℝ)^3931
        have hw : |(2622798109/5000000000 : ℝ)|=(2622798109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1570743747/5000000000 : ℝ)|^4955 ≤ (1161749131133/5000000000000 : ℝ)^3931
        have hw : |(1570743747/5000000000 : ℝ)|=(1570743747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1659_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180830391/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (627/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (23167/100000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4951/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4951 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4951*1^1024 ≤ 0^1024*1^4951 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4951 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4951/1024 : ℝ) ≤ (595587544702176883/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4951 ≤ (595587544702176883/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4951*50000000000000000000^1024 ≤ 595587544702176883^1024*5^4951 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 595587544702176883 50000000000000000000 4951 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (595587544702176883/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4951/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4951 := by
      have hnat : (1 : ℕ)^1024*1^4951 ≤ 1^4951*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4951 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50595587544702176883/50000000000000000000 : ℝ) ≤ (10024521142580883/10000000000000000 : ℝ) ^ (4951/1024 : ℝ) := by
    have hpowers : (50595587544702176883/50000000000000000000 : ℝ)^1024 ≤ (10024521142580883/10000000000000000 : ℝ)^4951 := by
      have hnat : (50595587544702176883 : ℕ)^1024*10000000000000000^4951 ≤ 10024521142580883^4951*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50595587544702176883 50000000000000000000 10024521142580883 10000000000000000 1024 4951 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10024521142580883/10000000000000000 : ℝ)) (X := (50595587544702176883/50000000000000000000 : ℝ)) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25595587544702176883/25000000000000000000 : ℝ) ≤ (5024521142580883/5000000000000000 : ℝ) ^ (4951/1024 : ℝ) := by
    have hpowers : (25595587544702176883/25000000000000000000 : ℝ)^1024 ≤ (5024521142580883/5000000000000000 : ℝ)^4951 := by
      have hnat : (25595587544702176883 : ℕ)^1024*5000000000000000^4951 ≤ 5024521142580883^4951*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25595587544702176883 25000000000000000000 5024521142580883 5000000000000000 1024 4951 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5024521142580883/5000000000000000 : ℝ)) (X := (25595587544702176883/25000000000000000000 : ℝ)) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(24521142580883/4000000000000000 : ℝ)*(0 : ℝ))^(4951/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(24521142580883/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(595587544702176883/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(24521142580883/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4951/1024 : ℝ) := by
    rw [show (1 : ℝ)+(24521142580883/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10024521142580883/10000000000000000 : ℝ) by norm_num, show 1+(595587544702176883/50000000000000000000 : ℝ)+(0 : ℝ)=(50595587544702176883/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(595587544702176883/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(24521142580883/4000000000000000 : ℝ)*(2/5 : ℝ))^(4951/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(24521142580883/4000000000000000 : ℝ)*(2/5 : ℝ)=(5024521142580883/5000000000000000 : ℝ) by norm_num, show 1+2*(595587544702176883/50000000000000000000 : ℝ)=(25595587544702176883/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(24521142580883/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4951/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (24521142580883/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(24521142580883/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4951/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (24521142580883/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(24521142580883/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4951/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (24521142580883/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-92312111/625000000 : ℝ)*X 0 0+(5774257583/10000000000 : ℝ)*X 0 1+(4927606309/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2716992329/5000000000 : ℝ)*X 1 0+(-970449339/5000000000 : ℝ)*X 1 1+(4927606937/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2716992973/5000000000 : ℝ)*X 2 0+(985521207/2000000000 : ℝ)*X 2 1+(-60653067/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2043211469/5000000000 : ℝ)*X 0 0+(616985059/2000000000 : ℝ)*X 0 1+(1325070251/2500000000 : ℝ)*X 0 2+(2043211469/5000000000 : ℝ)*X 1 0+(616985059/2000000000 : ℝ)*X 1 1+(1325070251/2500000000 : ℝ)*X 1 2+(2043211469/5000000000 : ℝ)*X 2 0+(616985059/2000000000 : ℝ)*X 2 1+(1325070251/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-739595421/5000000000 : ℝ)*X 0 0+(4948505267/10000000000 : ℝ)*X 0 1+(2876321017/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1040604931/2000000000 : ℝ)*X 1 0+(-1115864879/10000000000 : ℝ)*X 1 1+(2876320233/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5203023693/10000000000 : ℝ)*X 2 0+(71908021/125000000 : ℝ)*X 2 1+(-557932227/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4092168373/10000000000 : ℝ)*X 0 0+(2622798109/5000000000 : ℝ)*X 0 1+(1570743747/5000000000 : ℝ)*X 0 2+(4092168373/10000000000 : ℝ)*X 1 0+(2622798109/5000000000 : ℝ)*X 1 1+(1570743747/5000000000 : ℝ)*X 1 2+(4092168373/10000000000 : ℝ)*X 2 0+(2622798109/5000000000 : ℝ)*X 2 1+(1570743747/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (544675556485726272976383/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (135409211/100000000000000 : ℝ)*(base1) + (973304011/100000000000000 : ℝ)*(base19) + (249606497/20000000000000 : ℝ)*(base23) + (5231429/100000000000000 : ℝ)*(base24) + (23735923/10000000000000 : ℝ)*(upper5) + (816265972223083/100000000000000 : ℝ)*(major0) + (816265972223083/100000000000000 : ℝ)*(major1) + (204066493055771/25000000000000 : ℝ)*(major2) + (1181127158289833/100000000000000 : ℝ)*(sp0) + (1181132123845479/100000000000000 : ℝ)*(sp1) + (147641480485697/12500000000000 : ℝ)*(sp2) + (451396896008261/100000000000000 : ℝ)*(sp3) + (1518567217/25000000000000 : ℝ)*(sp4) + (1634320681/100000000000000 : ℝ)*(sp7) + (56424833217269/12500000000000 : ℝ)*(f.failure) + (118113309714949/10000000000000 : ℝ)*(f.sum) + (965962189974539/400000000000000000000000000000 : ℝ)*base66 + (481186587374207/100000000000000000000000000000 : ℝ)*base68 + (1953387100322289/400000000000000000000000000000 : ℝ)*base69 + (605161203874207/100000000000000000000000000000 : ℝ)*base72 + (1243459439574539/400000000000000000000000000000 : ℝ)*base74 + (3225093534722289/400000000000000000000000000000 : ℝ)*base75 + (1312147443677711/400000000000000000000000000000 : ℝ)*base78 + (414415398077711/400000000000000000000000000000 : ℝ)*base80 + (208469655677711/200000000000000000000000000000 : ℝ)*base82 + (3722179/1250000000000000000000 : ℝ)*base89 + (3722179/1250000000000000000000 : ℝ)*base91 + (8777821/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (277314045780097187254059/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (578884189/100000000000000 : ℝ)*(base19) + (307554307/50000000000000 : ℝ)*(base23) + (142029573/100000000000000 : ℝ)*(base39) + (31027527/50000000000000 : ℝ)*(upper2) + (32373237/20000000000000 : ℝ)*(upper5) + (429707236477091/50000000000000 : ℝ)*(major0) + (429707236477091/50000000000000 : ℝ)*(major1) + (859414330924609/100000000000000 : ℝ)*(major2) + (3947/640000000 : ℝ)*(sp1) + (763758689/100000000000000 : ℝ)*(sp2) + (621784321477357/50000000000000 : ℝ)*(sp4) + (621783723675887/50000000000000 : ℝ)*(sp5) + (155445925764623/12500000000000 : ℝ)*(sp6) + (475259976048043/100000000000000 : ℝ)*(sp7) + (475259976048043/100000000000000 : ℝ)*(f.failure) + (1243568784984287/100000000000000 : ℝ)*(f.sum) + (1087536905352453/400000000000000000000000000000 : ℝ)*base65 + (944058047150253/400000000000000000000000000000 : ℝ)*base68 + (511700059548647/200000000000000000000000000000 : ℝ)*base70 + (713746154049747/400000000000000000000000000000 : ℝ)*base71 + (466754565447547/400000000000000000000000000000 : ℝ)*base74 + (565818508851353/200000000000000000000000000000 : ℝ)*base75 + (470441704948647/200000000000000000000000000000 : ℝ)*base78 + (695492077748647/200000000000000000000000000000 : ℝ)*base80 + (50436984948647/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (50474813/10000000000000000000000 : ℝ)*base89 + (50474813/10000000000000000000000 : ℝ)*base91 + (50474813/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1659_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180830391/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (627/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (23167/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1659_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1659_s1_0 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1579208657/10000000000 : ℝ)*x 0 + (5489677283/10000000000 : ℝ)*x 1 + (5145673017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1579208657/10000000000 : ℝ)^4955 ≤ (9764234694937/100000000000000 : ℝ)^3931 := by
    have hnat : (1579208657 : ℕ)^4955*100000000000000^3931 ≤ 9764234694937^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1579208657 10000000000 9764234694937 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5489677283/10000000000 : ℝ)^4955 ≤ (11739252882693/25000000000000 : ℝ)^3931 := by
    have hnat : (5489677283 : ℕ)^4955*25000000000000^3931 ≤ 11739252882693^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489677283 10000000000 11739252882693 25000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5145673017/10000000000 : ℝ)^4955 ≤ (5409844220809/12500000000000 : ℝ)^3931 := by
    have hnat : (5145673017 : ℕ)^4955*12500000000000^3931 ≤ 5409844220809^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5145673017 10000000000 5409844220809 12500000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1579208657/10000000000 : ℝ), (5489677283/10000000000 : ℝ), (5145673017/10000000000 : ℝ)] ![(9764234694937/100000000000000 : ℝ), (11739252882693/25000000000000 : ℝ), (5409844220809/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1579208657/10000000000 : ℝ)|^4955 ≤ (9764234694937/100000000000000 : ℝ)^3931
        have hw : |(-1579208657/10000000000 : ℝ)|=(1579208657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5489677283/10000000000 : ℝ)|^4955 ≤ (11739252882693/25000000000000 : ℝ)^3931
        have hw : |(5489677283/10000000000 : ℝ)|=(5489677283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5145673017/10000000000 : ℝ)|^4955 ≤ (5409844220809/12500000000000 : ℝ)^3931
        have hw : |(5145673017/10000000000 : ℝ)|=(5145673017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s1_1 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5358287007/10000000000 : ℝ)*x 0 + (-878922659/5000000000 : ℝ)*x 1 + (5145672817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358287007/10000000000 : ℝ)^4955 ≤ (45544820586529/100000000000000 : ℝ)^3931 := by
    have hnat : (5358287007 : ℕ)^4955*100000000000000^3931 ≤ 45544820586529^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358287007 10000000000 45544820586529 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (878922659/5000000000 : ℝ)^4955 ≤ (5588213879931/50000000000000 : ℝ)^3931 := by
    have hnat : (878922659 : ℕ)^4955*50000000000000^3931 ≤ 5588213879931^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      878922659 5000000000 5588213879931 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5145672817/10000000000 : ℝ)^4955 ≤ (43278751646143/100000000000000 : ℝ)^3931 := by
    have hnat : (5145672817 : ℕ)^4955*100000000000000^3931 ≤ 43278751646143^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5145672817 10000000000 43278751646143 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358287007/10000000000 : ℝ), (-878922659/5000000000 : ℝ), (5145672817/10000000000 : ℝ)] ![(45544820586529/100000000000000 : ℝ), (5588213879931/50000000000000 : ℝ), (43278751646143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358287007/10000000000 : ℝ)|^4955 ≤ (45544820586529/100000000000000 : ℝ)^3931
        have hw : |(5358287007/10000000000 : ℝ)|=(5358287007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-878922659/5000000000 : ℝ)|^4955 ≤ (5588213879931/50000000000000 : ℝ)^3931
        have hw : |(-878922659/5000000000 : ℝ)|=(878922659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5145672817/10000000000 : ℝ)|^4955 ≤ (43278751646143/100000000000000 : ℝ)^3931
        have hw : |(5145672817/10000000000 : ℝ)|=(5145672817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s1_2 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2679143229/5000000000 : ℝ)*x 0 + (2572836699/5000000000 : ℝ)*x 1 + (-1757845283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2679143229/5000000000 : ℝ)^4955 ≤ (11386203676129/25000000000000 : ℝ)^3931 := by
    have hnat : (2679143229 : ℕ)^4955*25000000000000^3931 ≤ 11386203676129^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2679143229 5000000000 11386203676129 25000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2572836699/5000000000 : ℝ)^4955 ≤ (21639378902849/50000000000000 : ℝ)^3931 := by
    have hnat : (2572836699 : ℕ)^4955*50000000000000^3931 ≤ 21639378902849^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2572836699 5000000000 21639378902849 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1757845283/10000000000 : ℝ)^4955 ≤ (11176427479363/100000000000000 : ℝ)^3931 := by
    have hnat : (1757845283 : ℕ)^4955*100000000000000^3931 ≤ 11176427479363^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1757845283 10000000000 11176427479363 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2679143229/5000000000 : ℝ), (2572836699/5000000000 : ℝ), (-1757845283/10000000000 : ℝ)] ![(11386203676129/25000000000000 : ℝ), (21639378902849/50000000000000 : ℝ), (11176427479363/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2679143229/5000000000 : ℝ)|^4955 ≤ (11386203676129/25000000000000 : ℝ)^3931
        have hw : |(2679143229/5000000000 : ℝ)|=(2679143229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2572836699/5000000000 : ℝ)|^4955 ≤ (21639378902849/50000000000000 : ℝ)^3931
        have hw : |(2572836699/5000000000 : ℝ)|=(2572836699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1757845283/10000000000 : ℝ)|^4955 ≤ (11176427479363/100000000000000 : ℝ)^3931
        have hw : |(-1757845283/10000000000 : ℝ)|=(1757845283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s1_3 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2083572197/5000000000 : ℝ)*x 0 + (1867221667/5000000000 : ℝ)*x 1 + (4634567853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2083572197/5000000000 : ℝ)^4955 ≤ (33174849201963/100000000000000 : ℝ)^3931 := by
    have hnat : (2083572197 : ℕ)^4955*100000000000000^3931 ≤ 33174849201963^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083572197 5000000000 33174849201963 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1867221667/5000000000 : ℝ)^4955 ≤ (14446528320861/50000000000000 : ℝ)^3931 := by
    have hnat : (1867221667 : ℕ)^4955*50000000000000^3931 ≤ 14446528320861^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867221667 5000000000 14446528320861 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4634567853/10000000000 : ℝ)^4955 ≤ (18966047070959/50000000000000 : ℝ)^3931 := by
    have hnat : (4634567853 : ℕ)^4955*50000000000000^3931 ≤ 18966047070959^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4634567853 10000000000 18966047070959 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2083572197/5000000000 : ℝ), (1867221667/5000000000 : ℝ), (4634567853/10000000000 : ℝ)] ![(33174849201963/100000000000000 : ℝ), (14446528320861/50000000000000 : ℝ), (18966047070959/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2083572197/5000000000 : ℝ)|^4955 ≤ (33174849201963/100000000000000 : ℝ)^3931
        have hw : |(2083572197/5000000000 : ℝ)|=(2083572197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1867221667/5000000000 : ℝ)|^4955 ≤ (14446528320861/50000000000000 : ℝ)^3931
        have hw : |(1867221667/5000000000 : ℝ)|=(1867221667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4634567853/10000000000 : ℝ)|^4955 ≤ (18966047070959/50000000000000 : ℝ)^3931
        have hw : |(4634567853/10000000000 : ℝ)|=(4634567853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s1_4 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-789676719/5000000000 : ℝ)*x 0 + (2574557853/5000000000 : ℝ)*x 1 + (5486186903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (789676719/5000000000 : ℝ)^4955 ≤ (9765363076721/100000000000000 : ℝ)^3931 := by
    have hnat : (789676719 : ℕ)^4955*100000000000000^3931 ≤ 9765363076721^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      789676719 5000000000 9765363076721 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2574557853/5000000000 : ℝ)^4955 ≤ (43315255106209/100000000000000 : ℝ)^3931 := by
    have hnat : (2574557853 : ℕ)^4955*100000000000000^3931 ≤ 43315255106209^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2574557853 5000000000 43315255106209 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5486186903/10000000000 : ℝ)^4955 ≤ (46919381810549/100000000000000 : ℝ)^3931 := by
    have hnat : (5486186903 : ℕ)^4955*100000000000000^3931 ≤ 46919381810549^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486186903 10000000000 46919381810549 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-789676719/5000000000 : ℝ), (2574557853/5000000000 : ℝ), (5486186903/10000000000 : ℝ)] ![(9765363076721/100000000000000 : ℝ), (43315255106209/100000000000000 : ℝ), (46919381810549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-789676719/5000000000 : ℝ)|^4955 ≤ (9765363076721/100000000000000 : ℝ)^3931
        have hw : |(-789676719/5000000000 : ℝ)|=(789676719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2574557853/5000000000 : ℝ)|^4955 ≤ (43315255106209/100000000000000 : ℝ)^3931
        have hw : |(2574557853/5000000000 : ℝ)|=(2574557853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5486186903/10000000000 : ℝ)|^4955 ≤ (46919381810549/100000000000000 : ℝ)^3931
        have hw : |(5486186903/10000000000 : ℝ)|=(5486186903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s1_5 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5266227139/10000000000 : ℝ)*x 0 + (-1417331439/10000000000 : ℝ)*x 1 + (2743093479/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5266227139/10000000000 : ℝ)^4955 ≤ (44560703212097/100000000000000 : ℝ)^3931 := by
    have hnat : (5266227139 : ℕ)^4955*100000000000000^3931 ≤ 44560703212097^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266227139 10000000000 44560703212097 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1417331439/10000000000 : ℝ)^4955 ≤ (2129978593481/25000000000000 : ℝ)^3931 := by
    have hnat : (1417331439 : ℕ)^4955*25000000000000^3931 ≤ 2129978593481^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1417331439 10000000000 2129978593481 25000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2743093479/5000000000 : ℝ)^4955 ≤ (23459691201727/50000000000000 : ℝ)^3931 := by
    have hnat : (2743093479 : ℕ)^4955*50000000000000^3931 ≤ 23459691201727^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2743093479 5000000000 23459691201727 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5266227139/10000000000 : ℝ), (-1417331439/10000000000 : ℝ), (2743093479/5000000000 : ℝ)] ![(44560703212097/100000000000000 : ℝ), (2129978593481/25000000000000 : ℝ), (23459691201727/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5266227139/10000000000 : ℝ)|^4955 ≤ (44560703212097/100000000000000 : ℝ)^3931
        have hw : |(5266227139/10000000000 : ℝ)|=(5266227139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1417331439/10000000000 : ℝ)|^4955 ≤ (2129978593481/25000000000000 : ℝ)^3931
        have hw : |(-1417331439/10000000000 : ℝ)|=(1417331439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2743093479/5000000000 : ℝ)|^4955 ≤ (23459691201727/50000000000000 : ℝ)^3931
        have hw : |(2743093479/5000000000 : ℝ)|=(2743093479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s1_6 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1316556731/2500000000 : ℝ)*x 0 + (1371546809/2500000000 : ℝ)*x 1 + (-283466269/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1316556731/2500000000 : ℝ)^4955 ≤ (5570087614869/12500000000000 : ℝ)^3931 := by
    have hnat : (1316556731 : ℕ)^4955*12500000000000^3931 ≤ 5570087614869^3931*2500000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316556731 2500000000 5570087614869 12500000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1371546809/2500000000 : ℝ)^4955 ≤ (46919385400319/100000000000000 : ℝ)^3931 := by
    have hnat : (1371546809 : ℕ)^4955*100000000000000^3931 ≤ 46919385400319^3931*2500000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371546809 2500000000 46919385400319 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283466269/2000000000 : ℝ)^4955 ≤ (4259956830837/50000000000000 : ℝ)^3931 := by
    have hnat : (283466269 : ℕ)^4955*50000000000000^3931 ≤ 4259956830837^3931*2000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283466269 2000000000 4259956830837 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1316556731/2500000000 : ℝ), (1371546809/2500000000 : ℝ), (-283466269/2000000000 : ℝ)] ![(5570087614869/12500000000000 : ℝ), (46919385400319/100000000000000 : ℝ), (4259956830837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1316556731/2500000000 : ℝ)|^4955 ≤ (5570087614869/12500000000000 : ℝ)^3931
        have hw : |(1316556731/2500000000 : ℝ)|=(1316556731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1371546809/2500000000 : ℝ)|^4955 ≤ (46919385400319/100000000000000 : ℝ)^3931
        have hw : |(1371546809/2500000000 : ℝ)|=(1371546809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-283466269/2000000000 : ℝ)|^4955 ≤ (4259956830837/50000000000000 : ℝ)^3931
        have hw : |(-283466269/2000000000 : ℝ)|=(283466269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s1_7 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (166700947/400000000 : ℝ)*x 0 + (2312780091/5000000000 : ℝ)*x 1 + (467947079/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (166700947/400000000 : ℝ)^4955 ≤ (16589327638117/50000000000000 : ℝ)^3931 := by
    have hnat : (166700947 : ℕ)^4955*50000000000000^3931 ≤ 16589327638117^3931*400000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166700947 400000000 16589327638117 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2312780091/5000000000 : ℝ)^4955 ≤ (18919594398613/50000000000000 : ℝ)^3931 := by
    have hnat : (2312780091 : ℕ)^4955*50000000000000^3931 ≤ 18919594398613^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2312780091 5000000000 18919594398613 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (467947079/1250000000 : ℝ)^4955 ≤ (28982155901171/100000000000000 : ℝ)^3931 := by
    have hnat : (467947079 : ℕ)^4955*100000000000000^3931 ≤ 28982155901171^3931*1250000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467947079 1250000000 28982155901171 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(166700947/400000000 : ℝ), (2312780091/5000000000 : ℝ), (467947079/1250000000 : ℝ)] ![(16589327638117/50000000000000 : ℝ), (18919594398613/50000000000000 : ℝ), (28982155901171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(166700947/400000000 : ℝ)|^4955 ≤ (16589327638117/50000000000000 : ℝ)^3931
        have hw : |(166700947/400000000 : ℝ)|=(166700947/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2312780091/5000000000 : ℝ)|^4955 ≤ (18919594398613/50000000000000 : ℝ)^3931
        have hw : |(2312780091/5000000000 : ℝ)|=(2312780091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(467947079/1250000000 : ℝ)|^4955 ≤ (28982155901171/100000000000000 : ℝ)^3931
        have hw : |(467947079/1250000000 : ℝ)|=(467947079/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1659_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180830391/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23167/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (627/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (2469/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17189/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (23167/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (627/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (23167/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (627/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (23167/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (627/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (23167/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (627/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (23167/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (627/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (23167/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (627/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (627/12500 : ℝ) ^ (4951/1024 : ℝ) ≤ (52033065671523/100000000000000000000 : ℝ) := by
    have hpowers : (627/12500 : ℝ)^4951 ≤ (52033065671523/100000000000000000000 : ℝ)^1024 := by
      have hnat : (627 : ℕ)^4951*100000000000000000000^1024 ≤ 52033065671523^1024*12500^4951 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        627 12500 52033065671523 100000000000000000000 4951 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (627/12500 : ℝ)) (X := (52033065671523/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (23167/100000 : ℝ) ^ (4951/1024 : ℝ) ≤ (5309459393337917/6250000000000000000 : ℝ) := by
    have hpowers : (23167/100000 : ℝ)^4951 ≤ (5309459393337917/6250000000000000000 : ℝ)^1024 := by
      have hnat : (23167 : ℕ)^4951*6250000000000000000^1024 ≤ 5309459393337917^1024*100000^4951 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23167 100000 5309459393337917 6250000000000000000 4951 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23167/100000 : ℝ)) (X := (5309459393337917/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000052033065671523/50000000000000000000 : ℝ) ≤ (2500000538091671/2500000000000000 : ℝ) ^ (4951/1024 : ℝ) := by
    have hpowers : (50000052033065671523/50000000000000000000 : ℝ)^1024 ≤ (2500000538091671/2500000000000000 : ℝ)^4951 := by
      have hnat : (50000052033065671523 : ℕ)^1024*2500000000000000^4951 ≤ 2500000538091671^4951*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000052033065671523 50000000000000000000 2500000538091671 2500000000000000 1024 4951 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000538091671/2500000000000000 : ℝ)) (X := (50000052033065671523/50000000000000000000 : ℝ)) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20017000676671815639/20000000000000000000 : ℝ) ≤ (10001757506282869/10000000000000000 : ℝ) ^ (4951/1024 : ℝ) := by
    have hpowers : (20017000676671815639/20000000000000000000 : ℝ)^1024 ≤ (10001757506282869/10000000000000000 : ℝ)^4951 := by
      have hnat : (20017000676671815639 : ℕ)^1024*10000000000000000^4951 ≤ 10001757506282869^4951*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20017000676671815639 20000000000000000000 10001757506282869 10000000000000000 1024 4951 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001757506282869/10000000000000000 : ℝ)) (X := (20017000676671815639/20000000000000000000 : ℝ)) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3130309459393337917/3125000000000000000 : ℝ) ≤ (5001756430099527/5000000000000000 : ℝ) ^ (4951/1024 : ℝ) := by
    have hpowers : (3130309459393337917/3125000000000000000 : ℝ)^1024 ≤ (5001756430099527/5000000000000000 : ℝ)^4951 := by
      have hnat : (3130309459393337917 : ℕ)^1024*5000000000000000^4951 ≤ 5001756430099527^4951*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3130309459393337917 3125000000000000000 5001756430099527 5000000000000000 1024 4951 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001756430099527/5000000000000000 : ℝ)) (X := (3130309459393337917/3125000000000000000 : ℝ)) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(52033065671523/100000000000000000000 : ℝ) ≤ ((45373107339280128341/45377500000000000000 : ℝ)+2*(351070783237/363020000000000 : ℝ)*(627/12500 : ℝ))^(4951/1024 : ℝ) := by
    rw [show (45373107339280128341/45377500000000000000 : ℝ)+2*(351070783237/363020000000000 : ℝ)*(627/12500 : ℝ)=(2500000538091671/2500000000000000 : ℝ) by norm_num, show 1+2*(52033065671523/100000000000000000000 : ℝ)=(50000052033065671523/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5309459393337917/6250000000000000000 : ℝ)+(52033065671523/100000000000000000000 : ℝ) ≤ ((45373107339280128341/45377500000000000000 : ℝ)+(351070783237/363020000000000 : ℝ)*((23167/100000 : ℝ)+(627/12500 : ℝ)))^(4951/1024 : ℝ) := by
    rw [show (45373107339280128341/45377500000000000000 : ℝ)+(351070783237/363020000000000 : ℝ)*((23167/100000 : ℝ)+(627/12500 : ℝ))=(10001757506282869/10000000000000000 : ℝ) by norm_num, show 1+(5309459393337917/6250000000000000000 : ℝ)+(52033065671523/100000000000000000000 : ℝ)=(20017000676671815639/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5309459393337917/6250000000000000000 : ℝ) ≤ ((45373107339280128341/45377500000000000000 : ℝ)+2*(351070783237/363020000000000 : ℝ)*(23167/100000 : ℝ))^(4951/1024 : ℝ) := by
    rw [show (45373107339280128341/45377500000000000000 : ℝ)+2*(351070783237/363020000000000 : ℝ)*(23167/100000 : ℝ)=(5001756430099527/5000000000000000 : ℝ) by norm_num, show 1+2*(5309459393337917/6250000000000000000 : ℝ)=(3130309459393337917/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (45373107339280128341/45377500000000000000 : ℝ)*(X 1 0+X 2 0)+(351070783237/363020000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4951/1024 : ℝ)) (lo := (627/12500 : ℝ)) (hi := (23167/100000 : ℝ)) (c := (45373107339280128341/45377500000000000000 : ℝ)) (alpha := (351070783237/363020000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (45373107339280128341/45377500000000000000 : ℝ)*(X 0 1+X 2 1)+(351070783237/363020000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4951/1024 : ℝ)) (lo := (627/12500 : ℝ)) (hi := (23167/100000 : ℝ)) (c := (45373107339280128341/45377500000000000000 : ℝ)) (alpha := (351070783237/363020000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (45373107339280128341/45377500000000000000 : ℝ)*(X 0 2+X 1 2)+(351070783237/363020000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4951/1024 : ℝ)) (lo := (627/12500 : ℝ)) (hi := (23167/100000 : ℝ)) (c := (45373107339280128341/45377500000000000000 : ℝ)) (alpha := (351070783237/363020000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1579208657/10000000000 : ℝ)*X 0 0+(5489677283/10000000000 : ℝ)*X 0 1+(5145673017/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5358287007/10000000000 : ℝ)*X 1 0+(-878922659/5000000000 : ℝ)*X 1 1+(5145672817/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2679143229/5000000000 : ℝ)*X 2 0+(2572836699/5000000000 : ℝ)*X 2 1+(-1757845283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2083572197/5000000000 : ℝ)*X 0 0+(1867221667/5000000000 : ℝ)*X 0 1+(4634567853/10000000000 : ℝ)*X 0 2+(2083572197/5000000000 : ℝ)*X 1 0+(1867221667/5000000000 : ℝ)*X 1 1+(4634567853/10000000000 : ℝ)*X 1 2+(2083572197/5000000000 : ℝ)*X 2 0+(1867221667/5000000000 : ℝ)*X 2 1+(4634567853/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-789676719/5000000000 : ℝ)*X 0 0+(2574557853/5000000000 : ℝ)*X 0 1+(5486186903/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5266227139/10000000000 : ℝ)*X 1 0+(-1417331439/10000000000 : ℝ)*X 1 1+(2743093479/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1316556731/2500000000 : ℝ)*X 2 0+(1371546809/2500000000 : ℝ)*X 2 1+(-283466269/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((166700947/400000000 : ℝ)*X 0 0+(2312780091/5000000000 : ℝ)*X 0 1+(467947079/1250000000 : ℝ)*X 0 2+(166700947/400000000 : ℝ)*X 1 0+(2312780091/5000000000 : ℝ)*X 1 1+(467947079/1250000000 : ℝ)*X 1 2+(166700947/400000000 : ℝ)*X 2 0+(2312780091/5000000000 : ℝ)*X 2 1+(467947079/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6352934012476378267332180513/1134437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (841709607/50000000000000 : ℝ)*(base19) + (1242060243/100000000000000 : ℝ)*(base23) + (268298547/100000000000000 : ℝ)*(upper3) + (76900137/100000000000000 : ℝ)*(upper4) + (144719691/100000000000000 : ℝ)*(upper5) + (2008970634070263/100000000000000 : ℝ)*(major0) + (2008970634070263/100000000000000 : ℝ)*(major1) + (251121329258783/12500000000000 : ℝ)*(major2) + (145347854510219/5000000000000 : ℝ)*(sp0) + (1453484909395159/50000000000000 : ℝ)*(sp1) + (363371282518661/12500000000000 : ℝ)*(sp2) + (1110963115092461/100000000000000 : ℝ)*(sp3) + (450375161/3125000000000 : ℝ)*(sp4) + (404010587/6250000000000 : ℝ)*(sp7) + (1110969579261853/100000000000000 : ℝ)*(f.failure) + (726742875552383/25000000000000 : ℝ)*(f.sum) + (4872369937071/5186000000000000000000000000 : ℝ)*base66 + (49581517228244876317/4537750000000000000000000000000000 : ℝ)*base68 + (7054940439099001/4431396484375000000000000000000 : ℝ)*base69 + (50975497193192376317/4537750000000000000000000000000000 : ℝ)*base72 + (16569310977527/5186000000000000000000000000 : ℝ)*base74 + (69312485218433657/141804687500000000000000000000000 : ℝ)*base75 + (12684213465941501317/4537750000000000000000000000000000 : ℝ)*base78 + (53895531697542501317/4537750000000000000000000000000000 : ℝ)*base80 + (7810597562727/4537750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (69374523/10000000000000000000000 : ℝ)*base89 + (69374523/10000000000000000000000 : ℝ)*base91 + (30625477/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5117405383212884546835266193/2268875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (35252857/6250000000000 : ℝ)*(base19) + (11244519/2000000000000 : ℝ)*(base23) + (23086169/50000000000000 : ℝ)*(upper2) + (80237071/100000000000000 : ℝ)*(upper3) + (48198353/100000000000000 : ℝ)*(upper5) + (2050269389989403/100000000000000 : ℝ)*(major0) + (2050269389989403/100000000000000 : ℝ)*(major1) + (2050269389989403/100000000000000 : ℝ)*(major2) + (1399939191/25000000000000 : ℝ)*(sp1) + (3704413703/50000000000000 : ℝ)*(sp2) + (1483365366112517/50000000000000 : ℝ)*(sp4) + (2966724568422559/100000000000000 : ℝ)*(sp5) + (1483361380585839/50000000000000 : ℝ)*(sp6) + (22676159451421/2000000000000 : ℝ)*(sp7) + (22676159451421/2000000000000 : ℝ)*(f.failure) + (1483365366112517/50000000000000 : ℝ)*(f.sum) + (1476373272953/18151000000000000000000000000 : ℝ)*base65 + (34125568046982845423/4537750000000000000000000000000000 : ℝ)*base67 + (57664156044008345423/4537750000000000000000000000000000 : ℝ)*base69 + (20918956283996595423/4537750000000000000000000000000000 : ℝ)*base71 + (11469503369143/9075500000000000000000000000 : ℝ)*base74 + (643061772706345423/4537750000000000000000000000000000 : ℝ)*base75 + (29215177717491345423/4537750000000000000000000000000000 : ℝ)*base77 + (48736834482384845423/4537750000000000000000000000000000 : ℝ)*base79 + (60852125331919/18151000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1064389/200000000000000000000 : ℝ)*base90 + (1064389/200000000000000000000 : ℝ)*base92 + (1064389/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1659_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180830391/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23167/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (627/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2469/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17189/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1659_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1659_s2_0 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-396922959/2500000000 : ℝ)*x 0 + (5447932027/10000000000 : ℝ)*x 1 + (5181812199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (396922959/2500000000 : ℝ)^4955 ≤ (9830395577501/100000000000000 : ℝ)^3931 := by
    have hnat : (396922959 : ℕ)^4955*100000000000000^3931 ≤ 9830395577501^3931*2500000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396922959 2500000000 9830395577501 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5447932027/10000000000 : ℝ)^4955 ≤ (23253683034841/50000000000000 : ℝ)^3931 := by
    have hnat : (5447932027 : ℕ)^4955*50000000000000^3931 ≤ 23253683034841^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5447932027 10000000000 23253683034841 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181812199/10000000000 : ℝ)^4955 ≤ (43662238340823/100000000000000 : ℝ)^3931 := by
    have hnat : (5181812199 : ℕ)^4955*100000000000000^3931 ≤ 43662238340823^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181812199 10000000000 43662238340823 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-396922959/2500000000 : ℝ), (5447932027/10000000000 : ℝ), (5181812199/10000000000 : ℝ)] ![(9830395577501/100000000000000 : ℝ), (23253683034841/50000000000000 : ℝ), (43662238340823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-396922959/2500000000 : ℝ)|^4955 ≤ (9830395577501/100000000000000 : ℝ)^3931
        have hw : |(-396922959/2500000000 : ℝ)|=(396922959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5447932027/10000000000 : ℝ)|^4955 ≤ (23253683034841/50000000000000 : ℝ)^3931
        have hw : |(5447932027/10000000000 : ℝ)|=(5447932027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181812199/10000000000 : ℝ)|^4955 ≤ (43662238340823/100000000000000 : ℝ)^3931
        have hw : |(5181812199/10000000000 : ℝ)|=(5181812199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s2_1 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347205277/10000000000 : ℝ)*x 0 + (-1379779/8000000 : ℝ)*x 1 + (5181812349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347205277/10000000000 : ℝ)^4955 ≤ (22713061192061/50000000000000 : ℝ)^3931 := by
    have hnat : (5347205277 : ℕ)^4955*50000000000000^3931 ≤ 22713061192061^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347205277 10000000000 22713061192061 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1379779/8000000 : ℝ)^4955 ≤ (2727909416351/25000000000000 : ℝ)^3931 := by
    have hnat : (1379779 : ℕ)^4955*25000000000000^3931 ≤ 2727909416351^3931*8000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1379779 8000000 2727909416351 25000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181812349/10000000000 : ℝ)^4955 ≤ (43662239933971/100000000000000 : ℝ)^3931 := by
    have hnat : (5181812349 : ℕ)^4955*100000000000000^3931 ≤ 43662239933971^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181812349 10000000000 43662239933971 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347205277/10000000000 : ℝ), (-1379779/8000000 : ℝ), (5181812349/10000000000 : ℝ)] ![(22713061192061/50000000000000 : ℝ), (2727909416351/25000000000000 : ℝ), (43662239933971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347205277/10000000000 : ℝ)|^4955 ≤ (22713061192061/50000000000000 : ℝ)^3931
        have hw : |(5347205277/10000000000 : ℝ)|=(5347205277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1379779/8000000 : ℝ)|^4955 ≤ (2727909416351/25000000000000 : ℝ)^3931
        have hw : |(-1379779/8000000 : ℝ)|=(1379779/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181812349/10000000000 : ℝ)|^4955 ≤ (43662239933971/100000000000000 : ℝ)^3931
        have hw : |(5181812349/10000000000 : ℝ)|=(5181812349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s2_2 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069440919/2000000000 : ℝ)*x 0 + (647726571/1250000000 : ℝ)*x 1 + (-2759559/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069440919/2000000000 : ℝ)^4955 ≤ (1135652877027/2500000000000 : ℝ)^3931 := by
    have hnat : (1069440919 : ℕ)^4955*2500000000000^3931 ≤ 1135652877027^3931*2000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069440919 2000000000 1135652877027 2500000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (647726571/1250000000 : ℝ)^4955 ≤ (43662242259967/100000000000000 : ℝ)^3931 := by
    have hnat : (647726571 : ℕ)^4955*100000000000000^3931 ≤ 43662242259967^3931*1250000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647726571 1250000000 43662242259967 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2759559/16000000 : ℝ)^4955 ≤ (5455821324777/50000000000000 : ℝ)^3931 := by
    have hnat : (2759559 : ℕ)^4955*50000000000000^3931 ≤ 5455821324777^3931*16000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759559 16000000 5455821324777 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069440919/2000000000 : ℝ), (647726571/1250000000 : ℝ), (-2759559/16000000 : ℝ)] ![(1135652877027/2500000000000 : ℝ), (43662242259967/100000000000000 : ℝ), (5455821324777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069440919/2000000000 : ℝ)|^4955 ≤ (1135652877027/2500000000000 : ℝ)^3931
        have hw : |(1069440919/2000000000 : ℝ)|=(1069440919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(647726571/1250000000 : ℝ)|^4955 ≤ (43662242259967/100000000000000 : ℝ)^3931
        have hw : |(647726571/1250000000 : ℝ)|=(647726571/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2759559/16000000 : ℝ)|^4955 ≤ (5455821324777/50000000000000 : ℝ)^3931
        have hw : |(-2759559/16000000 : ℝ)|=(2759559/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s2_3 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4173481283/10000000000 : ℝ)*x 0 + (1917855973/5000000000 : ℝ)*x 1 + (4532040601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4173481283/10000000000 : ℝ)^4955 ≤ (33238451542853/100000000000000 : ℝ)^3931 := by
    have hnat : (4173481283 : ℕ)^4955*100000000000000^3931 ≤ 33238451542853^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4173481283 10000000000 33238451542853 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1917855973/5000000000 : ℝ)^4955 ≤ (29884126339199/100000000000000 : ℝ)^3931 := by
    have hnat : (1917855973 : ℕ)^4955*100000000000000^3931 ≤ 29884126339199^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1917855973 5000000000 29884126339199 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4532040601/10000000000 : ℝ)^4955 ≤ (36877422100451/100000000000000 : ℝ)^3931 := by
    have hnat : (4532040601 : ℕ)^4955*100000000000000^3931 ≤ 36877422100451^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4532040601 10000000000 36877422100451 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4173481283/10000000000 : ℝ), (1917855973/5000000000 : ℝ), (4532040601/10000000000 : ℝ)] ![(33238451542853/100000000000000 : ℝ), (29884126339199/100000000000000 : ℝ), (36877422100451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4173481283/10000000000 : ℝ)|^4955 ≤ (33238451542853/100000000000000 : ℝ)^3931
        have hw : |(4173481283/10000000000 : ℝ)|=(4173481283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1917855973/5000000000 : ℝ)|^4955 ≤ (29884126339199/100000000000000 : ℝ)^3931
        have hw : |(1917855973/5000000000 : ℝ)|=(1917855973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4532040601/10000000000 : ℝ)|^4955 ≤ (36877422100451/100000000000000 : ℝ)^3931
        have hw : |(4532040601/10000000000 : ℝ)|=(4532040601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s2_4 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-317551741/2000000000 : ℝ)*x 0 + (2591938977/5000000000 : ℝ)*x 1 + (340365271/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (317551741/2000000000 : ℝ)^4955 ≤ (196618349197/2000000000000 : ℝ)^3931 := by
    have hnat : (317551741 : ℕ)^4955*2000000000000^3931 ≤ 196618349197^3931*2000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317551741 2000000000 196618349197 2000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591938977/5000000000 : ℝ)^4955 ≤ (21842089920099/50000000000000 : ℝ)^3931 := by
    have hnat : (2591938977 : ℕ)^4955*50000000000000^3931 ≤ 21842089920099^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591938977 5000000000 21842089920099 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (340365271/625000000 : ℝ)^4955 ≤ (46484902683737/100000000000000 : ℝ)^3931 := by
    have hnat : (340365271 : ℕ)^4955*100000000000000^3931 ≤ 46484902683737^3931*625000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340365271 625000000 46484902683737 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-317551741/2000000000 : ℝ), (2591938977/5000000000 : ℝ), (340365271/625000000 : ℝ)] ![(196618349197/2000000000000 : ℝ), (21842089920099/50000000000000 : ℝ), (46484902683737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-317551741/2000000000 : ℝ)|^4955 ≤ (196618349197/2000000000000 : ℝ)^3931
        have hw : |(-317551741/2000000000 : ℝ)|=(317551741/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591938977/5000000000 : ℝ)|^4955 ≤ (21842089920099/50000000000000 : ℝ)^3931
        have hw : |(2591938977/5000000000 : ℝ)|=(2591938977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(340365271/625000000 : ℝ)|^4955 ≤ (46484902683737/100000000000000 : ℝ)^3931
        have hw : |(340365271/625000000 : ℝ)|=(340365271/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s2_5 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276035021/10000000000 : ℝ)*x 0 + (-36517313/250000000 : ℝ)*x 1 + (5445843759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276035021/10000000000 : ℝ)^4955 ≤ (22332668697013/50000000000000 : ℝ)^3931 := by
    have hnat : (5276035021 : ℕ)^4955*50000000000000^3931 ≤ 22332668697013^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276035021 10000000000 22332668697013 50000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36517313/250000000 : ℝ)^4955 ≤ (2212441530623/25000000000000 : ℝ)^3931 := by
    have hnat : (36517313 : ℕ)^4955*25000000000000^3931 ≤ 2212441530623^3931*250000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36517313 250000000 2212441530623 25000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5445843759/10000000000 : ℝ)^4955 ≤ (46484896475573/100000000000000 : ℝ)^3931 := by
    have hnat : (5445843759 : ℕ)^4955*100000000000000^3931 ≤ 46484896475573^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445843759 10000000000 46484896475573 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276035021/10000000000 : ℝ), (-36517313/250000000 : ℝ), (5445843759/10000000000 : ℝ)] ![(22332668697013/50000000000000 : ℝ), (2212441530623/25000000000000 : ℝ), (46484896475573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276035021/10000000000 : ℝ)|^4955 ≤ (22332668697013/50000000000000 : ℝ)^3931
        have hw : |(5276035021/10000000000 : ℝ)|=(5276035021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-36517313/250000000 : ℝ)|^4955 ≤ (2212441530623/25000000000000 : ℝ)^3931
        have hw : |(-36517313/250000000 : ℝ)|=(36517313/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5445843759/10000000000 : ℝ)|^4955 ≤ (46484896475573/100000000000000 : ℝ)^3931
        have hw : |(5445843759/10000000000 : ℝ)|=(5445843759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s2_6 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2638017671/5000000000 : ℝ)*x 0 + (5445843619/10000000000 : ℝ)*x 1 + (-365173067/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2638017671/5000000000 : ℝ)^4955 ≤ (8933068163881/20000000000000 : ℝ)^3931 := by
    have hnat : (2638017671 : ℕ)^4955*20000000000000^3931 ≤ 8933068163881^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2638017671 5000000000 8933068163881 20000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5445843619/10000000000 : ℝ)^4955 ≤ (2324244748463/5000000000000 : ℝ)^3931 := by
    have hnat : (5445843619 : ℕ)^4955*5000000000000^3931 ≤ 2324244748463^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445843619 10000000000 2324244748463 5000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (365173067/2500000000 : ℝ)^4955 ≤ (8849764198009/100000000000000 : ℝ)^3931 := by
    have hnat : (365173067 : ℕ)^4955*100000000000000^3931 ≤ 8849764198009^3931*2500000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365173067 2500000000 8849764198009 100000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2638017671/5000000000 : ℝ), (5445843619/10000000000 : ℝ), (-365173067/2500000000 : ℝ)] ![(8933068163881/20000000000000 : ℝ), (2324244748463/5000000000000 : ℝ), (8849764198009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2638017671/5000000000 : ℝ)|^4955 ≤ (8933068163881/20000000000000 : ℝ)^3931
        have hw : |(2638017671/5000000000 : ℝ)|=(2638017671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5445843619/10000000000 : ℝ)|^4955 ≤ (2324244748463/5000000000000 : ℝ)^3931
        have hw : |(5445843619/10000000000 : ℝ)|=(5445843619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-365173067/2500000000 : ℝ)|^4955 ≤ (8849764198009/100000000000000 : ℝ)^3931
        have hw : |(-365173067/2500000000 : ℝ)|=(365173067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1659_s2_7 (p : ℝ) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4173658021/10000000000 : ℝ)*x 0 + (2263318171/5000000000 : ℝ)*x 1 + (3841173667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4173658021/10000000000 : ℝ)^4955 ≤ (1329609031787/4000000000000 : ℝ)^3931 := by
    have hnat : (4173658021 : ℕ)^4955*4000000000000^3931 ≤ 1329609031787^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4173658021 10000000000 1329609031787 4000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2263318171/5000000000 : ℝ)^4955 ≤ (3682200088387/10000000000000 : ℝ)^3931 := by
    have hnat : (2263318171 : ℕ)^4955*10000000000000^3931 ≤ 3682200088387^3931*5000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2263318171 5000000000 3682200088387 10000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3841173667/10000000000 : ℝ)^4955 ≤ (5987554662229/20000000000000 : ℝ)^3931 := by
    have hnat : (3841173667 : ℕ)^4955*20000000000000^3931 ≤ 5987554662229^3931*10000000000^4955 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3841173667 10000000000 5987554662229 20000000000000 4955 3931 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4955/1024 : ℝ)) 4955 3931 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4173658021/10000000000 : ℝ), (2263318171/5000000000 : ℝ), (3841173667/10000000000 : ℝ)] ![(1329609031787/4000000000000 : ℝ), (3682200088387/10000000000000 : ℝ), (5987554662229/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4173658021/10000000000 : ℝ)|^4955 ≤ (1329609031787/4000000000000 : ℝ)^3931
        have hw : |(4173658021/10000000000 : ℝ)|=(4173658021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2263318171/5000000000 : ℝ)|^4955 ≤ (3682200088387/10000000000000 : ℝ)^3931
        have hw : |(2263318171/5000000000 : ℝ)|=(2263318171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3841173667/10000000000 : ℝ)|^4955 ≤ (5987554662229/20000000000000 : ℝ)^3931
        have hw : |(3841173667/10000000000 : ℝ)|=(3841173667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1659_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180830391/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17189/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2469/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (333/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16317/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17189/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2469/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17189/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2469/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17189/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2469/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17189/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2469/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17189/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2469/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17189/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2469/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2469/25000 : ℝ) ^ (4951/1024 : ℝ) ≤ (688349191109657/50000000000000000000 : ℝ) := by
    have hpowers : (2469/25000 : ℝ)^4951 ≤ (688349191109657/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2469 : ℕ)^4951*50000000000000000000^1024 ≤ 688349191109657^1024*25000^4951 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2469 25000 688349191109657 50000000000000000000 4951 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2469/25000 : ℝ)) (X := (688349191109657/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17189/100000 : ℝ) ^ (4951/1024 : ℝ) ≤ (10033133347530701/50000000000000000000 : ℝ) := by
    have hpowers : (17189/100000 : ℝ)^4951 ≤ (10033133347530701/50000000000000000000 : ℝ)^1024 := by
      have hnat : (17189 : ℕ)^4951*50000000000000000000^1024 ≤ 10033133347530701^1024*100000^4951 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17189 100000 10033133347530701 50000000000000000000 4951 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17189/100000 : ℝ)) (X := (10033133347530701/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000688349191109657/25000000000000000000 : ℝ) ≤ (5000028473515449/5000000000000000 : ℝ) ^ (4951/1024 : ℝ) := by
    have hpowers : (25000688349191109657/25000000000000000000 : ℝ)^1024 ≤ (5000028473515449/5000000000000000 : ℝ)^4951 := by
      have hnat : (25000688349191109657 : ℕ)^1024*5000000000000000^4951 ≤ 5000028473515449^4951*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000688349191109657 25000000000000000000 5000028473515449 5000000000000000 1024 4951 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000028473515449/5000000000000000 : ℝ)) (X := (25000688349191109657/25000000000000000000 : ℝ)) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25005360741269320179/25000000000000000000 : ℝ) ≤ (10000443460496997/10000000000000000 : ℝ) ^ (4951/1024 : ℝ) := by
    have hpowers : (25005360741269320179/25000000000000000000 : ℝ)^1024 ≤ (10000443460496997/10000000000000000 : ℝ)^4951 := by
      have hnat : (25005360741269320179 : ℕ)^1024*10000000000000000^4951 ≤ 10000443460496997^4951*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005360741269320179 25000000000000000000 10000443460496997 10000000000000000 1024 4951 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000443460496997/10000000000000000 : ℝ)) (X := (25005360741269320179/25000000000000000000 : ℝ)) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010033133347530701/25000000000000000000 : ℝ) ≤ (1250103746745387/1250000000000000 : ℝ) ^ (4951/1024 : ℝ) := by
    have hpowers : (25010033133347530701/25000000000000000000 : ℝ)^1024 ≤ (1250103746745387/1250000000000000 : ℝ)^4951 := by
      have hnat : (25010033133347530701 : ℕ)^1024*1250000000000000^4951 ≤ 1250103746745387^4951*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010033133347530701 25000000000000000000 1250103746745387 1250000000000000 1024 4951 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250103746745387/1250000000000000 : ℝ)) (X := (25010033133347530701/25000000000000000000 : ℝ)) (by norm_num) 4951 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(688349191109657/50000000000000000000 : ℝ) ≤ ((36561391019827284813/36565000000000000000 : ℝ)+2*(386513466099/731300000000000 : ℝ)*(2469/25000 : ℝ))^(4951/1024 : ℝ) := by
    rw [show (36561391019827284813/36565000000000000000 : ℝ)+2*(386513466099/731300000000000 : ℝ)*(2469/25000 : ℝ)=(5000028473515449/5000000000000000 : ℝ) by norm_num, show 1+2*(688349191109657/50000000000000000000 : ℝ)=(25000688349191109657/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10033133347530701/50000000000000000000 : ℝ)+(688349191109657/50000000000000000000 : ℝ) ≤ ((36561391019827284813/36565000000000000000 : ℝ)+(386513466099/731300000000000 : ℝ)*((17189/100000 : ℝ)+(2469/25000 : ℝ)))^(4951/1024 : ℝ) := by
    rw [show (36561391019827284813/36565000000000000000 : ℝ)+(386513466099/731300000000000 : ℝ)*((17189/100000 : ℝ)+(2469/25000 : ℝ))=(10000443460496997/10000000000000000 : ℝ) by norm_num, show 1+(10033133347530701/50000000000000000000 : ℝ)+(688349191109657/50000000000000000000 : ℝ)=(25005360741269320179/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10033133347530701/50000000000000000000 : ℝ) ≤ ((36561391019827284813/36565000000000000000 : ℝ)+2*(386513466099/731300000000000 : ℝ)*(17189/100000 : ℝ))^(4951/1024 : ℝ) := by
    rw [show (36561391019827284813/36565000000000000000 : ℝ)+2*(386513466099/731300000000000 : ℝ)*(17189/100000 : ℝ)=(1250103746745387/1250000000000000 : ℝ) by norm_num, show 1+2*(10033133347530701/50000000000000000000 : ℝ)=(25010033133347530701/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (36561391019827284813/36565000000000000000 : ℝ)*(X 1 0+X 2 0)+(386513466099/731300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4951/1024 : ℝ)) (lo := (2469/25000 : ℝ)) (hi := (17189/100000 : ℝ)) (c := (36561391019827284813/36565000000000000000 : ℝ)) (alpha := (386513466099/731300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (36561391019827284813/36565000000000000000 : ℝ)*(X 0 1+X 2 1)+(386513466099/731300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4951/1024 : ℝ)) (lo := (2469/25000 : ℝ)) (hi := (17189/100000 : ℝ)) (c := (36561391019827284813/36565000000000000000 : ℝ)) (alpha := (386513466099/731300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (36561391019827284813/36565000000000000000 : ℝ)*(X 0 2+X 1 2)+(386513466099/731300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4951/1024 : ℝ)) (lo := (2469/25000 : ℝ)) (hi := (17189/100000 : ℝ)) (c := (36561391019827284813/36565000000000000000 : ℝ)) (alpha := (386513466099/731300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-396922959/2500000000 : ℝ)*X 0 0+(5447932027/10000000000 : ℝ)*X 0 1+(5181812199/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347205277/10000000000 : ℝ)*X 1 0+(-1379779/8000000 : ℝ)*X 1 1+(5181812349/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069440919/2000000000 : ℝ)*X 2 0+(647726571/1250000000 : ℝ)*X 2 1+(-2759559/16000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4173481283/10000000000 : ℝ)*X 0 0+(1917855973/5000000000 : ℝ)*X 0 1+(4532040601/10000000000 : ℝ)*X 0 2+(4173481283/10000000000 : ℝ)*X 1 0+(1917855973/5000000000 : ℝ)*X 1 1+(4532040601/10000000000 : ℝ)*X 1 2+(4173481283/10000000000 : ℝ)*X 2 0+(1917855973/5000000000 : ℝ)*X 2 1+(4532040601/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-317551741/2000000000 : ℝ)*X 0 0+(2591938977/5000000000 : ℝ)*X 0 1+(340365271/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5276035021/10000000000 : ℝ)*X 1 0+(-36517313/250000000 : ℝ)*X 1 1+(5445843759/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2638017671/5000000000 : ℝ)*X 2 0+(5445843619/10000000000 : ℝ)*X 2 1+(-365173067/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4173658021/10000000000 : ℝ)*X 0 0+(2263318171/5000000000 : ℝ)*X 0 1+(3841173667/10000000000 : ℝ)*X 0 2+(4173658021/10000000000 : ℝ)*X 1 0+(2263318171/5000000000 : ℝ)*X 1 1+(3841173667/10000000000 : ℝ)*X 1 2+(4173658021/10000000000 : ℝ)*X 2 0+(2263318171/5000000000 : ℝ)*X 2 1+(3841173667/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1659_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12908010744424534674194123529/914125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (916148883/50000000000000 : ℝ)*(base19) + (1351246593/100000000000000 : ℝ)*(base23) + (17243751/4000000000000 : ℝ)*(upper3) + (881683/6250000000000 : ℝ)*(lower4) + (2596937428924623/100000000000000 : ℝ)*(major0) + (2596937428924623/100000000000000 : ℝ)*(major1) + (162308589307789/6250000000000 : ℝ)*(major2) + (939434336305127/25000000000000 : ℝ)*(sp0) + (3757754757096089/100000000000000 : ℝ)*(sp1) + (117429785082279/3125000000000 : ℝ)*(sp2) + (1436109355273759/100000000000000 : ℝ)*(sp3) + (19244173347/100000000000000 : ℝ)*(sp4) + (1057757167/50000000000000 : ℝ)*(sp6) + (8442494329/100000000000000 : ℝ)*(sp7) + (179514724721011/12500000000000 : ℝ)*(f.failure) + (751551317878771/20000000000000 : ℝ)*(f.sum) + (58661693258663/73130000000000000000000000000 : ℝ)*base65 + (26361794186640549501/3656500000000000000000000000000000 : ℝ)*base68 + (620219563340055791/114265625000000000000000000000000 : ℝ)*base69 + (6231833202565049501/3656500000000000000000000000000000 : ℝ)*base72 + (136127688039793/73130000000000000000000000000 : ℝ)*base73 + (658716299435645083/57132812500000000000000000000000 : ℝ)*base75 + (184750395965024267/35500000000000000000000000000000 : ℝ)*base78 + (288072836689024267/35500000000000000000000000000000 : ℝ)*base80 + (1565317241309/355000000000000000000000000 : ℝ)*base81 + (2454699/1250000000000000000000 : ℝ)*base90 + (2454699/1250000000000000000000 : ℝ)*base92 + (14954699/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (471272599598133379932273/36565000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1388451687/100000000000000 : ℝ)*(base19) + (2238197249/100000000000000 : ℝ)*(base23) + (30755643/25000000000000 : ℝ)*(upper3) + (264543797/100000000000000 : ℝ)*(lower4) + (105745661/50000000000000 : ℝ)*(upper5) + (2638075348245851/100000000000000 : ℝ)*(major0) + (2638075348245851/100000000000000 : ℝ)*(major1) + (2638075348245851/100000000000000 : ℝ)*(major2) + (2736821993/25000000000000 : ℝ)*(sp1) + (9776859193/50000000000000 : ℝ)*(sp2) + (1908641509569103/50000000000000 : ℝ)*(sp4) + (3817270683398547/100000000000000 : ℝ)*(sp5) + (381726122722257/10000000000000 : ℝ)*(sp6) + (364716811933157/25000000000000 : ℝ)*(sp7) + (364716811933157/25000000000000 : ℝ)*(f.failure) + (1908641509569103/50000000000000 : ℝ)*(f.sum) + (7283991750979/36565000000000000000000000000 : ℝ)*base65 + (9502188104464989137/3656500000000000000000000000000000 : ℝ)*base68 + (544664354587010863/3656500000000000000000000000000000 : ℝ)*base69 + (4929642048838489137/3656500000000000000000000000000000 : ℝ)*base72 + (105461895975591/36565000000000000000000000000 : ℝ)*base74 + (53250067811365489137/3656500000000000000000000000000000 : ℝ)*base76 + (14136409778598010863/3656500000000000000000000000000000 : ℝ)*base77 + (28992546027334010863/3656500000000000000000000000000000 : ℝ)*base79 + (151520725687459/36565000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (28825613/2500000000000000000000 : ℝ)*base90 + (28825613/2500000000000000000000 : ℝ)*base92 + (28825613/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1659_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180830391/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17189/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2469/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (333/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16317/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1659_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1659_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180830391/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (333/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16317/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1659_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1659_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1659_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4951/1024 : ℝ) ≤ p) (hpb : p ≤ (4955/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (180830391/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (333/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16317/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1659_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
