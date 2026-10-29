-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1645_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:11:54.422581+00:00
-- url     : https://prove2.me/submissions/192b72bc-76bf-4867-ab47-412ad1851a71

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
theorem support_rectangle_w1645_s0_0 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-187683887/1250000000 : ℝ)*x 0 + (5791525357/10000000000 : ℝ)*x 1 + (4918143373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (187683887/1250000000 : ℝ)^4899 ≤ (4548570711307/50000000000000 : ℝ)^3875 := by
    have hnat : (187683887 : ℕ)^4899*50000000000000^3875 ≤ 4548570711307^3875*1250000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187683887 1250000000 4548570711307 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5791525357/10000000000 : ℝ)^4899 ≤ (25065657075973/50000000000000 : ℝ)^3875 := by
    have hnat : (5791525357 : ℕ)^4899*50000000000000^3875 ≤ 25065657075973^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5791525357 10000000000 25065657075973 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4918143373/10000000000 : ℝ)^4899 ≤ (2038577220931/5000000000000 : ℝ)^3875 := by
    have hnat : (4918143373 : ℕ)^4899*5000000000000^3875 ≤ 2038577220931^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4918143373 10000000000 2038577220931 5000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-187683887/1250000000 : ℝ), (5791525357/10000000000 : ℝ), (4918143373/10000000000 : ℝ)] ![(4548570711307/50000000000000 : ℝ), (25065657075973/50000000000000 : ℝ), (2038577220931/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-187683887/1250000000 : ℝ)|^4899 ≤ (4548570711307/50000000000000 : ℝ)^3875
        have hw : |(-187683887/1250000000 : ℝ)|=(187683887/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5791525357/10000000000 : ℝ)|^4899 ≤ (25065657075973/50000000000000 : ℝ)^3875
        have hw : |(5791525357/10000000000 : ℝ)|=(5791525357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4918143373/10000000000 : ℝ)|^4899 ≤ (2038577220931/5000000000000 : ℝ)^3875
        have hw : |(4918143373/10000000000 : ℝ)|=(4918143373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s0_1 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2719761567/5000000000 : ℝ)*x 0 + (-1981392141/10000000000 : ℝ)*x 1 + (1229536107/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2719761567/5000000000 : ℝ)^4899 ≤ (46310625233531/100000000000000 : ℝ)^3875 := by
    have hnat : (2719761567 : ℕ)^4899*100000000000000^3875 ≤ 46310625233531^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719761567 5000000000 46310625233531 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1981392141/10000000000 : ℝ)^4899 ≤ (12917819272039/100000000000000 : ℝ)^3875 := by
    have hnat : (1981392141 : ℕ)^4899*100000000000000^3875 ≤ 12917819272039^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981392141 10000000000 12917819272039 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1229536107/2500000000 : ℝ)^4899 ≤ (8154311095159/20000000000000 : ℝ)^3875 := by
    have hnat : (1229536107 : ℕ)^4899*20000000000000^3875 ≤ 8154311095159^3875*2500000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1229536107 2500000000 8154311095159 20000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2719761567/5000000000 : ℝ), (-1981392141/10000000000 : ℝ), (1229536107/2500000000 : ℝ)] ![(46310625233531/100000000000000 : ℝ), (12917819272039/100000000000000 : ℝ), (8154311095159/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2719761567/5000000000 : ℝ)|^4899 ≤ (46310625233531/100000000000000 : ℝ)^3875
        have hw : |(2719761567/5000000000 : ℝ)|=(2719761567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1981392141/10000000000 : ℝ)|^4899 ≤ (12917819272039/100000000000000 : ℝ)^3875
        have hw : |(-1981392141/10000000000 : ℝ)|=(1981392141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1229536107/2500000000 : ℝ)|^4899 ≤ (8154311095159/20000000000000 : ℝ)^3875
        have hw : |(1229536107/2500000000 : ℝ)|=(1229536107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s0_2 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1359881337/2500000000 : ℝ)*x 0 + (2459071491/5000000000 : ℝ)*x 1 + (-1981391089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1359881337/2500000000 : ℝ)^4899 ≤ (46310649064033/100000000000000 : ℝ)^3875 := by
    have hnat : (1359881337 : ℕ)^4899*100000000000000^3875 ≤ 46310649064033^3875*2500000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359881337 2500000000 46310649064033 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2459071491/5000000000 : ℝ)^4899 ≤ (40771540320653/100000000000000 : ℝ)^3875 := by
    have hnat : (2459071491 : ℕ)^4899*100000000000000^3875 ≤ 40771540320653^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2459071491 5000000000 40771540320653 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1981391089/10000000000 : ℝ)^4899 ≤ (12917810601019/100000000000000 : ℝ)^3875 := by
    have hnat : (1981391089 : ℕ)^4899*100000000000000^3875 ≤ 12917810601019^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981391089 10000000000 12917810601019 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1359881337/2500000000 : ℝ), (2459071491/5000000000 : ℝ), (-1981391089/10000000000 : ℝ)] ![(46310649064033/100000000000000 : ℝ), (40771540320653/100000000000000 : ℝ), (12917810601019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1359881337/2500000000 : ℝ)|^4899 ≤ (46310649064033/100000000000000 : ℝ)^3875
        have hw : |(1359881337/2500000000 : ℝ)|=(1359881337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2459071491/5000000000 : ℝ)|^4899 ≤ (40771540320653/100000000000000 : ℝ)^3875
        have hw : |(2459071491/5000000000 : ℝ)|=(2459071491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1981391089/10000000000 : ℝ)|^4899 ≤ (12917810601019/100000000000000 : ℝ)^3875
        have hw : |(-1981391089/10000000000 : ℝ)|=(1981391089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s0_3 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (818591963/2000000000 : ℝ)*x 0 + (1540696533/5000000000 : ℝ)*x 1 + (2663409539/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (818591963/2000000000 : ℝ)^4899 ≤ (2020204218401/6250000000000 : ℝ)^3875 := by
    have hnat : (818591963 : ℕ)^4899*6250000000000^3875 ≤ 2020204218401^3875*2000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      818591963 2000000000 2020204218401 6250000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1540696533/5000000000 : ℝ)^4899 ≤ (11287932498927/50000000000000 : ℝ)^3875 := by
    have hnat : (1540696533 : ℕ)^4899*50000000000000^3875 ≤ 11287932498927^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1540696533 5000000000 11287932498927 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2663409539/5000000000 : ℝ)^4899 ≤ (45100867499391/100000000000000 : ℝ)^3875 := by
    have hnat : (2663409539 : ℕ)^4899*100000000000000^3875 ≤ 45100867499391^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2663409539 5000000000 45100867499391 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(818591963/2000000000 : ℝ), (1540696533/5000000000 : ℝ), (2663409539/5000000000 : ℝ)] ![(2020204218401/6250000000000 : ℝ), (11287932498927/50000000000000 : ℝ), (45100867499391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(818591963/2000000000 : ℝ)|^4899 ≤ (2020204218401/6250000000000 : ℝ)^3875
        have hw : |(818591963/2000000000 : ℝ)|=(818591963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1540696533/5000000000 : ℝ)|^4899 ≤ (11287932498927/50000000000000 : ℝ)^3875
        have hw : |(1540696533/5000000000 : ℝ)|=(1540696533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2663409539/5000000000 : ℝ)|^4899 ≤ (45100867499391/100000000000000 : ℝ)^3875
        have hw : |(2663409539/5000000000 : ℝ)|=(2663409539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s0_4 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1503824471/10000000000 : ℝ)*x 0 + (4939867833/10000000000 : ℝ)*x 1 + (5769048073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1503824471/10000000000 : ℝ)^4899 ≤ (9115171796609/100000000000000 : ℝ)^3875 := by
    have hnat : (1503824471 : ℕ)^4899*100000000000000^3875 ≤ 9115171796609^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1503824471 10000000000 9115171796609 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4939867833/10000000000 : ℝ)^4899 ≤ (10249841363959/25000000000000 : ℝ)^3875 := by
    have hnat : (4939867833 : ℕ)^4899*25000000000000^3875 ≤ 10249841363959^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4939867833 10000000000 10249841363959 25000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5769048073/10000000000 : ℝ)^4899 ≤ (6235682841817/12500000000000 : ℝ)^3875 := by
    have hnat : (5769048073 : ℕ)^4899*12500000000000^3875 ≤ 6235682841817^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5769048073 10000000000 6235682841817 12500000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1503824471/10000000000 : ℝ), (4939867833/10000000000 : ℝ), (5769048073/10000000000 : ℝ)] ![(9115171796609/100000000000000 : ℝ), (10249841363959/25000000000000 : ℝ), (6235682841817/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1503824471/10000000000 : ℝ)|^4899 ≤ (9115171796609/100000000000000 : ℝ)^3875
        have hw : |(-1503824471/10000000000 : ℝ)|=(1503824471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4939867833/10000000000 : ℝ)|^4899 ≤ (10249841363959/25000000000000 : ℝ)^3875
        have hw : |(4939867833/10000000000 : ℝ)|=(4939867833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5769048073/10000000000 : ℝ)|^4899 ≤ (6235682841817/12500000000000 : ℝ)^3875
        have hw : |(5769048073/10000000000 : ℝ)|=(5769048073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s0_5 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5201159519/10000000000 : ℝ)*x 0 + (-565242903/5000000000 : ℝ)*x 1 + (5769049219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5201159519/10000000000 : ℝ)^4899 ≤ (43760004213389/100000000000000 : ℝ)^3875 := by
    have hnat : (5201159519 : ℕ)^4899*100000000000000^3875 ≤ 43760004213389^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5201159519 10000000000 43760004213389 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (565242903/5000000000 : ℝ)^4899 ≤ (3177260251067/50000000000000 : ℝ)^3875 := by
    have hnat : (565242903 : ℕ)^4899*50000000000000^3875 ≤ 3177260251067^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565242903 5000000000 3177260251067 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5769049219/10000000000 : ℝ)^4899 ≤ (2494273763139/5000000000000 : ℝ)^3875 := by
    have hnat : (5769049219 : ℕ)^4899*5000000000000^3875 ≤ 2494273763139^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5769049219 10000000000 2494273763139 5000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5201159519/10000000000 : ℝ), (-565242903/5000000000 : ℝ), (5769049219/10000000000 : ℝ)] ![(43760004213389/100000000000000 : ℝ), (3177260251067/50000000000000 : ℝ), (2494273763139/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5201159519/10000000000 : ℝ)|^4899 ≤ (43760004213389/100000000000000 : ℝ)^3875
        have hw : |(5201159519/10000000000 : ℝ)|=(5201159519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-565242903/5000000000 : ℝ)|^4899 ≤ (3177260251067/50000000000000 : ℝ)^3875
        have hw : |(-565242903/5000000000 : ℝ)|=(565242903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5769049219/10000000000 : ℝ)|^4899 ≤ (2494273763139/5000000000000 : ℝ)^3875
        have hw : |(5769049219/10000000000 : ℝ)|=(5769049219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s0_6 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5201160271/10000000000 : ℝ)*x 0 + (5769048309/10000000000 : ℝ)*x 1 + (-1130486081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5201160271/10000000000 : ℝ)^4899 ≤ (21880006106149/50000000000000 : ℝ)^3875 := by
    have hnat : (5201160271 : ℕ)^4899*50000000000000^3875 ≤ 21880006106149^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5201160271 10000000000 21880006106149 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5769048309/10000000000 : ℝ)^4899 ≤ (49885465314523/100000000000000 : ℝ)^3875 := by
    have hnat : (5769048309 : ℕ)^4899*100000000000000^3875 ≤ 49885465314523^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5769048309 10000000000 49885465314523 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1130486081/10000000000 : ℝ)^4899 ≤ (6354522456411/100000000000000 : ℝ)^3875 := by
    have hnat : (1130486081 : ℕ)^4899*100000000000000^3875 ≤ 6354522456411^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1130486081 10000000000 6354522456411 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5201160271/10000000000 : ℝ), (5769048309/10000000000 : ℝ), (-1130486081/10000000000 : ℝ)] ![(21880006106149/50000000000000 : ℝ), (49885465314523/100000000000000 : ℝ), (6354522456411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5201160271/10000000000 : ℝ)|^4899 ≤ (21880006106149/50000000000000 : ℝ)^3875
        have hw : |(5201160271/10000000000 : ℝ)|=(5201160271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5769048309/10000000000 : ℝ)|^4899 ≤ (49885465314523/100000000000000 : ℝ)^3875
        have hw : |(5769048309/10000000000 : ℝ)|=(5769048309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1130486081/10000000000 : ℝ)|^4899 ≤ (6354522456411/100000000000000 : ℝ)^3875
        have hw : |(-1130486081/10000000000 : ℝ)|=(1130486081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s0_7 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (204950681/500000000 : ℝ)*x 0 + (1054193929/2000000000 : ℝ)*x 1 + (1569587807/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (204950681/500000000 : ℝ)^4899 ≤ (8095930433771/25000000000000 : ℝ)^3875 := by
    have hnat : (204950681 : ℕ)^4899*25000000000000^3875 ≤ 8095930433771^3875*500000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204950681 500000000 8095930433771 25000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054193929/2000000000 : ℝ)^4899 ≤ (44503876420649/100000000000000 : ℝ)^3875 := by
    have hnat : (1054193929 : ℕ)^4899*100000000000000^3875 ≤ 44503876420649^3875*2000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054193929 2000000000 44503876420649 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1569587807/5000000000 : ℝ)^4899 ≤ (11556200915459/50000000000000 : ℝ)^3875 := by
    have hnat : (1569587807 : ℕ)^4899*50000000000000^3875 ≤ 11556200915459^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1569587807 5000000000 11556200915459 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(204950681/500000000 : ℝ), (1054193929/2000000000 : ℝ), (1569587807/5000000000 : ℝ)] ![(8095930433771/25000000000000 : ℝ), (44503876420649/100000000000000 : ℝ), (11556200915459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(204950681/500000000 : ℝ)|^4899 ≤ (8095930433771/25000000000000 : ℝ)^3875
        have hw : |(204950681/500000000 : ℝ)|=(204950681/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1054193929/2000000000 : ℝ)|^4899 ≤ (44503876420649/100000000000000 : ℝ)^3875
        have hw : |(1054193929/2000000000 : ℝ)|=(1054193929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1569587807/5000000000 : ℝ)|^4899 ≤ (11556200915459/50000000000000 : ℝ)^3875
        have hw : |(1569587807/5000000000 : ℝ)|=(1569587807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1645_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35709611/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2373/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2933/12500 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4895/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4895 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4895*1^1024 ≤ 0^1024*1^4895 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4895 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4895/1024 : ℝ) ≤ (156548157247100589/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4895 ≤ (156548157247100589/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4895*12500000000000000000^1024 ≤ 156548157247100589^1024*5^4895 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 156548157247100589 12500000000000000000 4895 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (156548157247100589/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4895/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4895 := by
      have hnat : (1 : ℕ)^1024*1^4895 ≤ 1^4895*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4895 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12656548157247100589/12500000000000000000 : ℝ) ≤ (2005214050856341/2000000000000000 : ℝ) ^ (4895/1024 : ℝ) := by
    have hpowers : (12656548157247100589/12500000000000000000 : ℝ)^1024 ≤ (2005214050856341/2000000000000000 : ℝ)^4895 := by
      have hnat : (12656548157247100589 : ℕ)^1024*2000000000000000^4895 ≤ 2005214050856341^4895*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12656548157247100589 12500000000000000000 2005214050856341 2000000000000000 1024 4895 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2005214050856341/2000000000000000 : ℝ)) (X := (12656548157247100589/12500000000000000000 : ℝ)) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6406548157247100589/6250000000000000000 : ℝ) ≤ (1005214050856341/1000000000000000 : ℝ) ^ (4895/1024 : ℝ) := by
    have hpowers : (6406548157247100589/6250000000000000000 : ℝ)^1024 ≤ (1005214050856341/1000000000000000 : ℝ)^4895 := by
      have hnat : (6406548157247100589 : ℕ)^1024*1000000000000000^4895 ≤ 1005214050856341^4895*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6406548157247100589 6250000000000000000 1005214050856341 1000000000000000 1024 4895 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1005214050856341/1000000000000000 : ℝ)) (X := (6406548157247100589/6250000000000000000 : ℝ)) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(5214050856341/800000000000000 : ℝ)*(0 : ℝ))^(4895/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5214050856341/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(156548157247100589/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(5214050856341/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4895/1024 : ℝ) := by
    rw [show (1 : ℝ)+(5214050856341/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2005214050856341/2000000000000000 : ℝ) by norm_num, show 1+(156548157247100589/12500000000000000000 : ℝ)+(0 : ℝ)=(12656548157247100589/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(156548157247100589/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(5214050856341/800000000000000 : ℝ)*(2/5 : ℝ))^(4895/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5214050856341/800000000000000 : ℝ)*(2/5 : ℝ)=(1005214050856341/1000000000000000 : ℝ) by norm_num, show 1+2*(156548157247100589/12500000000000000000 : ℝ)=(6406548157247100589/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(5214050856341/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4895/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5214050856341/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(5214050856341/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4895/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5214050856341/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(5214050856341/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4895/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5214050856341/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-187683887/1250000000 : ℝ)*X 0 0+(5791525357/10000000000 : ℝ)*X 0 1+(4918143373/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2719761567/5000000000 : ℝ)*X 1 0+(-1981392141/10000000000 : ℝ)*X 1 1+(1229536107/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1359881337/2500000000 : ℝ)*X 2 0+(2459071491/5000000000 : ℝ)*X 2 1+(-1981391089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((818591963/2000000000 : ℝ)*X 0 0+(1540696533/5000000000 : ℝ)*X 0 1+(2663409539/5000000000 : ℝ)*X 0 2+(818591963/2000000000 : ℝ)*X 1 0+(1540696533/5000000000 : ℝ)*X 1 1+(2663409539/5000000000 : ℝ)*X 1 2+(818591963/2000000000 : ℝ)*X 2 0+(1540696533/5000000000 : ℝ)*X 2 1+(2663409539/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1503824471/10000000000 : ℝ)*X 0 0+(4939867833/10000000000 : ℝ)*X 0 1+(5769048073/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5201159519/10000000000 : ℝ)*X 1 0+(-565242903/5000000000 : ℝ)*X 1 1+(5769049219/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5201160271/10000000000 : ℝ)*X 2 0+(5769048309/10000000000 : ℝ)*X 2 1+(-1130486081/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((204950681/500000000 : ℝ)*X 0 0+(1054193929/2000000000 : ℝ)*X 0 1+(1569587807/5000000000 : ℝ)*X 0 2+(204950681/500000000 : ℝ)*X 1 0+(1054193929/2000000000 : ℝ)*X 1 1+(1569587807/5000000000 : ℝ)*X 1 2+(204950681/500000000 : ℝ)*X 2 0+(1054193929/2000000000 : ℝ)*X 2 1+(1569587807/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (406476042486797373341649/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1516918533/100000000000000 : ℝ)*(base19) + (55560207/3125000000000 : ℝ)*(base23) + (68389781/100000000000000 : ℝ)*(upper3) + (13940537/12500000000000 : ℝ)*(upper4) + (187406297/50000000000000 : ℝ)*(upper5) + (795172217188463/100000000000000 : ℝ)*(major0) + (795172217188463/100000000000000 : ℝ)*(major1) + (795172217188463/100000000000000 : ℝ)*(major2) + (286244921317181/25000000000000 : ℝ)*(sp0) + (286246960932709/25000000000000 : ℝ)*(sp1) + (228997516544549/20000000000000 : ℝ)*(sp2) + (111338126090129/25000000000000 : ℝ)*(sp3) + (4837690323/50000000000000 : ℝ)*(sp4) + (2230636997/100000000000000 : ℝ)*(sp7) + (55669341874689/12500000000000 : ℝ)*(f.failure) + (1144989360649369/100000000000000 : ℝ)*(f.sum) + (138497579193883/40000000000000000000000000000 : ℝ)*base65 + (689154080966117/80000000000000000000000000000 : ℝ)*base68 + (442845593686117/80000000000000000000000000000 : ℝ)*base70 + (34686639273883/80000000000000000000000000000 : ℝ)*base71 + (98766594206117/40000000000000000000000000000 : ℝ)*base74 + (53744758473883/80000000000000000000000000000 : ℝ)*base75 + (115288220393883/80000000000000000000000000000 : ℝ)*base77 + (142140561286117/80000000000000000000000000000 : ℝ)*base80 + (10323308446117/40000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (2564021/250000000000000000000 : ℝ)*base90 + (2564021/250000000000000000000 : ℝ)*base92 + (2564021/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (48599708991733332990129/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22254313/1250000000000 : ℝ)*(base19) + (1976898337/100000000000000 : ℝ)*(base23) + (44788719/50000000000000 : ℝ)*(base32) + (345265463/100000000000000 : ℝ)*(upper3) + (145423573/100000000000000 : ℝ)*(upper5) + (209387246486259/25000000000000 : ℝ)*(major0) + (209387246486259/25000000000000 : ℝ)*(major1) + (209387246486259/25000000000000 : ℝ)*(major2) + (401189399/6250000000000 : ℝ)*(sp1) + (3451535803/50000000000000 : ℝ)*(sp2) + (301502203946843/25000000000000 : ℝ)*(sp4) + (301500154102987/25000000000000 : ℝ)*(sp5) + (120599993581743/10000000000000 : ℝ)*(sp6) + (469088742527193/100000000000000 : ℝ)*(sp7) + (58636104013079/12500000000000 : ℝ)*(f.failure) + (301502203946843/25000000000000 : ℝ)*(f.sum) + (972355038319/10000000000000000000000000000 : ℝ)*base65 + (274773012298319/20000000000000000000000000000 : ℝ)*base67 + (214546126358319/20000000000000000000000000000 : ℝ)*base69 + (164586136958319/20000000000000000000000000000 : ℝ)*base71 + (49487896988319/10000000000000000000000000000 : ℝ)*base73 + (154353430198319/20000000000000000000000000000 : ℝ)*base75 + (81807017958319/20000000000000000000000000000 : ℝ)*base77 + (177649210578319/20000000000000000000000000000 : ℝ)*base79 + (21102632138319/10000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2269/250000000000000000000 : ℝ)*base89 + (2269/250000000000000000000 : ℝ)*base91 + (2269/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1645_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35709611/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2373/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2933/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1645_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1645_s1_0 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-80471403/500000000 : ℝ)*x 0 + (2750041557/5000000000 : ℝ)*x 1 + (5139462519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (80471403/500000000 : ℝ)^4899 ≤ (9931803835311/100000000000000 : ℝ)^3875 := by
    have hnat : (80471403 : ℕ)^4899*100000000000000^3875 ≤ 9931803835311^3875*500000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80471403 500000000 9931803835311 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2750041557/5000000000 : ℝ)^4899 ≤ (46963421905483/100000000000000 : ℝ)^3875 := by
    have hnat : (2750041557 : ℕ)^4899*100000000000000^3875 ≤ 46963421905483^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750041557 5000000000 46963421905483 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5139462519/10000000000 : ℝ)^4899 ≤ (43104774251829/100000000000000 : ℝ)^3875 := by
    have hnat : (5139462519 : ℕ)^4899*100000000000000^3875 ≤ 43104774251829^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139462519 10000000000 43104774251829 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-80471403/500000000 : ℝ), (2750041557/5000000000 : ℝ), (5139462519/10000000000 : ℝ)] ![(9931803835311/100000000000000 : ℝ), (46963421905483/100000000000000 : ℝ), (43104774251829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-80471403/500000000 : ℝ)|^4899 ≤ (9931803835311/100000000000000 : ℝ)^3875
        have hw : |(-80471403/500000000 : ℝ)|=(80471403/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2750041557/5000000000 : ℝ)|^4899 ≤ (46963421905483/100000000000000 : ℝ)^3875
        have hw : |(2750041557/5000000000 : ℝ)|=(2750041557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5139462519/10000000000 : ℝ)|^4899 ≤ (43104774251829/100000000000000 : ℝ)^3875
        have hw : |(5139462519/10000000000 : ℝ)|=(5139462519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s1_1 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2681003203/5000000000 : ℝ)*x 0 + (-56157283/312500000 : ℝ)*x 1 + (5139462343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2681003203/5000000000 : ℝ)^4899 ≤ (45477846577131/100000000000000 : ℝ)^3875 := by
    have hnat : (2681003203 : ℕ)^4899*100000000000000^3875 ≤ 45477846577131^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2681003203 5000000000 45477846577131 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56157283/312500000 : ℝ)^4899 ≤ (1141738102431/10000000000000 : ℝ)^3875 := by
    have hnat : (56157283 : ℕ)^4899*10000000000000^3875 ≤ 1141738102431^3875*312500000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56157283 312500000 1141738102431 10000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5139462343/10000000000 : ℝ)^4899 ≤ (21552386192819/50000000000000 : ℝ)^3875 := by
    have hnat : (5139462343 : ℕ)^4899*50000000000000^3875 ≤ 21552386192819^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139462343 10000000000 21552386192819 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2681003203/5000000000 : ℝ), (-56157283/312500000 : ℝ), (5139462343/10000000000 : ℝ)] ![(45477846577131/100000000000000 : ℝ), (1141738102431/10000000000000 : ℝ), (21552386192819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2681003203/5000000000 : ℝ)|^4899 ≤ (45477846577131/100000000000000 : ℝ)^3875
        have hw : |(2681003203/5000000000 : ℝ)|=(2681003203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-56157283/312500000 : ℝ)|^4899 ≤ (1141738102431/10000000000000 : ℝ)^3875
        have hw : |(-56157283/312500000 : ℝ)|=(56157283/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5139462343/10000000000 : ℝ)|^4899 ≤ (21552386192819/50000000000000 : ℝ)^3875
        have hw : |(5139462343/10000000000 : ℝ)|=(5139462343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s1_2 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072401507/2000000000 : ℝ)*x 0 + (2569730533/5000000000 : ℝ)*x 1 + (-449258309/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072401507/2000000000 : ℝ)^4899 ≤ (1819114347327/4000000000000 : ℝ)^3875 := by
    have hnat : (1072401507 : ℕ)^4899*4000000000000^3875 ≤ 1819114347327^3875*2000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072401507 2000000000 1819114347327 4000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2569730533/5000000000 : ℝ)^4899 ≤ (43104758845151/100000000000000 : ℝ)^3875 := by
    have hnat : (2569730533 : ℕ)^4899*100000000000000^3875 ≤ 43104758845151^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569730533 5000000000 43104758845151 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449258309/2500000000 : ℝ)^4899 ≤ (2283476494029/20000000000000 : ℝ)^3875 := by
    have hnat : (449258309 : ℕ)^4899*20000000000000^3875 ≤ 2283476494029^3875*2500000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449258309 2500000000 2283476494029 20000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072401507/2000000000 : ℝ), (2569730533/5000000000 : ℝ), (-449258309/2500000000 : ℝ)] ![(1819114347327/4000000000000 : ℝ), (43104758845151/100000000000000 : ℝ), (2283476494029/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072401507/2000000000 : ℝ)|^4899 ≤ (1819114347327/4000000000000 : ℝ)^3875
        have hw : |(1072401507/2000000000 : ℝ)|=(1072401507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2569730533/5000000000 : ℝ)|^4899 ≤ (43104758845151/100000000000000 : ℝ)^3875
        have hw : |(2569730533/5000000000 : ℝ)|=(2569730533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-449258309/2500000000 : ℝ)|^4899 ≤ (2283476494029/20000000000000 : ℝ)^3875
        have hw : |(-449258309/2500000000 : ℝ)|=(449258309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s1_3 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4176778329/10000000000 : ℝ)*x 0 + (3731957001/10000000000 : ℝ)*x 1 + (4659100323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4176778329/10000000000 : ℝ)^4899 ≤ (33162381889643/100000000000000 : ℝ)^3875 := by
    have hnat : (4176778329 : ℕ)^4899*100000000000000^3875 ≤ 33162381889643^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4176778329 10000000000 33162381889643 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3731957001/10000000000 : ℝ)^4899 ≤ (28761890855969/100000000000000 : ℝ)^3875 := by
    have hnat : (3731957001 : ℕ)^4899*100000000000000^3875 ≤ 28761890855969^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3731957001 10000000000 28761890855969 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4659100323/10000000000 : ℝ)^4899 ≤ (38075727236781/100000000000000 : ℝ)^3875 := by
    have hnat : (4659100323 : ℕ)^4899*100000000000000^3875 ≤ 38075727236781^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4659100323 10000000000 38075727236781 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4176778329/10000000000 : ℝ), (3731957001/10000000000 : ℝ), (4659100323/10000000000 : ℝ)] ![(33162381889643/100000000000000 : ℝ), (28761890855969/100000000000000 : ℝ), (38075727236781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4176778329/10000000000 : ℝ)|^4899 ≤ (33162381889643/100000000000000 : ℝ)^3875
        have hw : |(4176778329/10000000000 : ℝ)|=(4176778329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3731957001/10000000000 : ℝ)|^4899 ≤ (28761890855969/100000000000000 : ℝ)^3875
        have hw : |(3731957001/10000000000 : ℝ)|=(3731957001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4659100323/10000000000 : ℝ)|^4899 ≤ (38075727236781/100000000000000 : ℝ)^3875
        have hw : |(4659100323/10000000000 : ℝ)|=(4659100323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s1_4 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1609591783/10000000000 : ℝ)*x 0 + (5143150611/10000000000 : ℝ)*x 1 + (5496341519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1609591783/10000000000 : ℝ)^4899 ≤ (9933081179181/100000000000000 : ℝ)^3875 := by
    have hnat : (1609591783 : ℕ)^4899*100000000000000^3875 ≤ 9933081179181^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1609591783 10000000000 9933081179181 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5143150611/10000000000 : ℝ)^4899 ≤ (8628776823411/20000000000000 : ℝ)^3875 := by
    have hnat : (5143150611 : ℕ)^4899*20000000000000^3875 ≤ 8628776823411^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5143150611 10000000000 8628776823411 20000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5496341519/10000000000 : ℝ)^4899 ≤ (9384606937367/20000000000000 : ℝ)^3875 := by
    have hnat : (5496341519 : ℕ)^4899*20000000000000^3875 ≤ 9384606937367^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496341519 10000000000 9384606937367 20000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1609591783/10000000000 : ℝ), (5143150611/10000000000 : ℝ), (5496341519/10000000000 : ℝ)] ![(9933081179181/100000000000000 : ℝ), (8628776823411/20000000000000 : ℝ), (9384606937367/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1609591783/10000000000 : ℝ)|^4899 ≤ (9933081179181/100000000000000 : ℝ)^3875
        have hw : |(-1609591783/10000000000 : ℝ)|=(1609591783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5143150611/10000000000 : ℝ)|^4899 ≤ (8628776823411/20000000000000 : ℝ)^3875
        have hw : |(5143150611/10000000000 : ℝ)|=(5143150611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5496341519/10000000000 : ℝ)|^4899 ≤ (9384606937367/20000000000000 : ℝ)^3875
        have hw : |(5496341519/10000000000 : ℝ)|=(5496341519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s1_5 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1053127223/2000000000 : ℝ)*x 0 + (-144015337/1000000000 : ℝ)*x 1 + (219853661/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053127223/2000000000 : ℝ)^4899 ≤ (11111737963983/25000000000000 : ℝ)^3875 := by
    have hnat : (1053127223 : ℕ)^4899*25000000000000^3875 ≤ 11111737963983^3875*2000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053127223 2000000000 11111737963983 25000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (144015337/1000000000 : ℝ)^4899 ≤ (539375836009/6250000000000 : ℝ)^3875 := by
    have hnat : (144015337 : ℕ)^4899*6250000000000^3875 ≤ 539375836009^3875*1000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144015337 1000000000 539375836009 6250000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219853661/400000000 : ℝ)^4899 ≤ (46923034751593/100000000000000 : ℝ)^3875 := by
    have hnat : (219853661 : ℕ)^4899*100000000000000^3875 ≤ 46923034751593^3875*400000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219853661 400000000 46923034751593 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053127223/2000000000 : ℝ), (-144015337/1000000000 : ℝ), (219853661/400000000 : ℝ)] ![(11111737963983/25000000000000 : ℝ), (539375836009/6250000000000 : ℝ), (46923034751593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053127223/2000000000 : ℝ)|^4899 ≤ (11111737963983/25000000000000 : ℝ)^3875
        have hw : |(1053127223/2000000000 : ℝ)|=(1053127223/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-144015337/1000000000 : ℝ)|^4899 ≤ (539375836009/6250000000000 : ℝ)^3875
        have hw : |(-144015337/1000000000 : ℝ)|=(144015337/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(219853661/400000000 : ℝ)|^4899 ≤ (46923034751593/100000000000000 : ℝ)^3875
        have hw : |(219853661/400000000 : ℝ)|=(219853661/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s1_6 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1316408987/2500000000 : ℝ)*x 0 + (5496341771/10000000000 : ℝ)*x 1 + (-180019157/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1316408987/2500000000 : ℝ)^4899 ≤ (22223475036893/50000000000000 : ℝ)^3875 := by
    have hnat : (1316408987 : ℕ)^4899*50000000000000^3875 ≤ 22223475036893^3875*2500000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316408987 2500000000 22223475036893 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5496341771/10000000000 : ℝ)^4899 ≤ (11730759351677/25000000000000 : ℝ)^3875 := by
    have hnat : (5496341771 : ℕ)^4899*25000000000000^3875 ≤ 11730759351677^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496341771 10000000000 11730759351677 25000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (180019157/1250000000 : ℝ)^4899 ≤ (8630012512483/100000000000000 : ℝ)^3875 := by
    have hnat : (180019157 : ℕ)^4899*100000000000000^3875 ≤ 8630012512483^3875*1250000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180019157 1250000000 8630012512483 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1316408987/2500000000 : ℝ), (5496341771/10000000000 : ℝ), (-180019157/1250000000 : ℝ)] ![(22223475036893/50000000000000 : ℝ), (11730759351677/25000000000000 : ℝ), (8630012512483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1316408987/2500000000 : ℝ)|^4899 ≤ (22223475036893/50000000000000 : ℝ)^3875
        have hw : |(1316408987/2500000000 : ℝ)|=(1316408987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5496341771/10000000000 : ℝ)|^4899 ≤ (11730759351677/25000000000000 : ℝ)^3875
        have hw : |(5496341771/10000000000 : ℝ)|=(5496341771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-180019157/1250000000 : ℝ)|^4899 ≤ (8630012512483/100000000000000 : ℝ)^3875
        have hw : |(-180019157/1250000000 : ℝ)|=(180019157/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s1_7 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4177195639/10000000000 : ℝ)*x 0 + (4649617081/10000000000 : ℝ)*x 1 + (3741577029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4177195639/10000000000 : ℝ)^4899 ≤ (33166570833569/100000000000000 : ℝ)^3875 := by
    have hnat : (4177195639 : ℕ)^4899*100000000000000^3875 ≤ 33166570833569^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4177195639 10000000000 33166570833569 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4649617081/10000000000 : ℝ)^4899 ≤ (37977773312803/100000000000000 : ℝ)^3875 := by
    have hnat : (4649617081 : ℕ)^4899*100000000000000^3875 ≤ 37977773312803^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4649617081 10000000000 37977773312803 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3741577029/10000000000 : ℝ)^4899 ≤ (28855655837249/100000000000000 : ℝ)^3875 := by
    have hnat : (3741577029 : ℕ)^4899*100000000000000^3875 ≤ 28855655837249^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3741577029 10000000000 28855655837249 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4177195639/10000000000 : ℝ), (4649617081/10000000000 : ℝ), (3741577029/10000000000 : ℝ)] ![(33166570833569/100000000000000 : ℝ), (37977773312803/100000000000000 : ℝ), (28855655837249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4177195639/10000000000 : ℝ)|^4899 ≤ (33166570833569/100000000000000 : ℝ)^3875
        have hw : |(4177195639/10000000000 : ℝ)|=(4177195639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4649617081/10000000000 : ℝ)|^4899 ≤ (37977773312803/100000000000000 : ℝ)^3875
        have hw : |(4649617081/10000000000 : ℝ)|=(4649617081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3741577029/10000000000 : ℝ)|^4899 ≤ (28855655837249/100000000000000 : ℝ)^3875
        have hw : |(3741577029/10000000000 : ℝ)|=(3741577029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1645_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35709611/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2933/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2373/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1211/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4337/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2933/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2373/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2933/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2373/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2933/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2373/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2933/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2373/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2933/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2373/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2933/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2373/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2373/50000 : ℝ) ^ (4895/1024 : ℝ) ≤ (23520937648897/50000000000000000000 : ℝ) := by
    have hpowers : (2373/50000 : ℝ)^4895 ≤ (23520937648897/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2373 : ℕ)^4895*50000000000000000000^1024 ≤ 23520937648897^1024*50000^4895 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2373 50000 23520937648897 50000000000000000000 4895 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2373/50000 : ℝ)) (X := (23520937648897/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2933/12500 : ℝ) ^ (4895/1024 : ℝ) ≤ (48901214749248059/50000000000000000000 : ℝ) := by
    have hpowers : (2933/12500 : ℝ)^4895 ≤ (48901214749248059/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2933 : ℕ)^4895*50000000000000000000^1024 ≤ 48901214749248059^1024*12500^4895 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2933 12500 48901214749248059 50000000000000000000 4895 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2933/12500 : ℝ)) (X := (48901214749248059/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000023520937648897/25000000000000000000 : ℝ) ≤ (10000001968165981/10000000000000000 : ℝ) ^ (4895/1024 : ℝ) := by
    have hpowers : (25000023520937648897/25000000000000000000 : ℝ)^1024 ≤ (10000001968165981/10000000000000000 : ℝ)^4895 := by
      have hnat : (25000023520937648897 : ℕ)^1024*10000000000000000^4895 ≤ 10000001968165981^4895*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000023520937648897 25000000000000000000 10000001968165981 10000000000000000 1024 4895 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001968165981/10000000000000000 : ℝ)) (X := (25000023520937648897/25000000000000000000 : ℝ)) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12512231183921724239/12500000000000000000 : ℝ) ≤ (5001023075737921/5000000000000000 : ℝ) ^ (4895/1024 : ℝ) := by
    have hpowers : (12512231183921724239/12500000000000000000 : ℝ)^1024 ≤ (5001023075737921/5000000000000000 : ℝ)^4895 := by
      have hnat : (12512231183921724239 : ℕ)^1024*5000000000000000^4895 ≤ 5001023075737921^4895*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12512231183921724239 12500000000000000000 5001023075737921 5000000000000000 1024 4895 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001023075737921/5000000000000000 : ℝ)) (X := (12512231183921724239/12500000000000000000 : ℝ)) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25048901214749248059/25000000000000000000 : ℝ) ≤ (10004090334785703/10000000000000000 : ℝ) ^ (4895/1024 : ℝ) := by
    have hpowers : (25048901214749248059/25000000000000000000 : ℝ)^1024 ≤ (10004090334785703/10000000000000000 : ℝ)^4895 := by
      have hnat : (25048901214749248059 : ℕ)^1024*10000000000000000^4895 ≤ 10004090334785703^4895*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25048901214749248059 25000000000000000000 10004090334785703 10000000000000000 1024 4895 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004090334785703/10000000000000000 : ℝ)) (X := (25048901214749248059/25000000000000000000 : ℝ)) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(23520937648897/50000000000000000000 : ℝ) ≤ ((1909802382164832977/1910000000000000000 : ℝ)+2*(292026187123/267400000000000 : ℝ)*(2373/50000 : ℝ))^(4895/1024 : ℝ) := by
    rw [show (1909802382164832977/1910000000000000000 : ℝ)+2*(292026187123/267400000000000 : ℝ)*(2373/50000 : ℝ)=(10000001968165981/10000000000000000 : ℝ) by norm_num, show 1+2*(23520937648897/50000000000000000000 : ℝ)=(25000023520937648897/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(48901214749248059/50000000000000000000 : ℝ)+(23520937648897/50000000000000000000 : ℝ) ≤ ((1909802382164832977/1910000000000000000 : ℝ)+(292026187123/267400000000000 : ℝ)*((2933/12500 : ℝ)+(2373/50000 : ℝ)))^(4895/1024 : ℝ) := by
    rw [show (1909802382164832977/1910000000000000000 : ℝ)+(292026187123/267400000000000 : ℝ)*((2933/12500 : ℝ)+(2373/50000 : ℝ))=(5001023075737921/5000000000000000 : ℝ) by norm_num, show 1+(48901214749248059/50000000000000000000 : ℝ)+(23520937648897/50000000000000000000 : ℝ)=(12512231183921724239/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(48901214749248059/50000000000000000000 : ℝ) ≤ ((1909802382164832977/1910000000000000000 : ℝ)+2*(292026187123/267400000000000 : ℝ)*(2933/12500 : ℝ))^(4895/1024 : ℝ) := by
    rw [show (1909802382164832977/1910000000000000000 : ℝ)+2*(292026187123/267400000000000 : ℝ)*(2933/12500 : ℝ)=(10004090334785703/10000000000000000 : ℝ) by norm_num, show 1+2*(48901214749248059/50000000000000000000 : ℝ)=(25048901214749248059/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1909802382164832977/1910000000000000000 : ℝ)*(X 1 0+X 2 0)+(292026187123/267400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4895/1024 : ℝ)) (lo := (2373/50000 : ℝ)) (hi := (2933/12500 : ℝ)) (c := (1909802382164832977/1910000000000000000 : ℝ)) (alpha := (292026187123/267400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1909802382164832977/1910000000000000000 : ℝ)*(X 0 1+X 2 1)+(292026187123/267400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4895/1024 : ℝ)) (lo := (2373/50000 : ℝ)) (hi := (2933/12500 : ℝ)) (c := (1909802382164832977/1910000000000000000 : ℝ)) (alpha := (292026187123/267400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1909802382164832977/1910000000000000000 : ℝ)*(X 0 2+X 1 2)+(292026187123/267400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4895/1024 : ℝ)) (lo := (2373/50000 : ℝ)) (hi := (2933/12500 : ℝ)) (c := (1909802382164832977/1910000000000000000 : ℝ)) (alpha := (292026187123/267400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-80471403/500000000 : ℝ)*X 0 0+(2750041557/5000000000 : ℝ)*X 0 1+(5139462519/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2681003203/5000000000 : ℝ)*X 1 0+(-56157283/312500000 : ℝ)*X 1 1+(5139462343/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1072401507/2000000000 : ℝ)*X 2 0+(2569730533/5000000000 : ℝ)*X 2 1+(-449258309/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4176778329/10000000000 : ℝ)*X 0 0+(3731957001/10000000000 : ℝ)*X 0 1+(4659100323/10000000000 : ℝ)*X 0 2+(4176778329/10000000000 : ℝ)*X 1 0+(3731957001/10000000000 : ℝ)*X 1 1+(4659100323/10000000000 : ℝ)*X 1 2+(4176778329/10000000000 : ℝ)*X 2 0+(3731957001/10000000000 : ℝ)*X 2 1+(4659100323/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1609591783/10000000000 : ℝ)*X 0 0+(5143150611/10000000000 : ℝ)*X 0 1+(5496341519/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1053127223/2000000000 : ℝ)*X 1 0+(-144015337/1000000000 : ℝ)*X 1 1+(219853661/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1316408987/2500000000 : ℝ)*X 2 0+(5496341771/10000000000 : ℝ)*X 2 1+(-180019157/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4177195639/10000000000 : ℝ)*X 0 0+(4649617081/10000000000 : ℝ)*X 0 1+(3741577029/10000000000 : ℝ)*X 0 2+(4177195639/10000000000 : ℝ)*X 1 0+(4649617081/10000000000 : ℝ)*X 1 1+(3741577029/10000000000 : ℝ)*X 1 2+(4177195639/10000000000 : ℝ)*X 2 0+(4649617081/10000000000 : ℝ)*X 2 1+(3741577029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (482797243920237940060367259/47750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (673148937/100000000000000 : ℝ)*(base1) + (1030853291/100000000000000 : ℝ)*(base19) + (1614722513/100000000000000 : ℝ)*(base23) + (98050473/100000000000000 : ℝ)*(upper3) + (15609311/20000000000000 : ℝ)*(upper5) + (1925789847184511/100000000000000 : ℝ)*(major0) + (1925789847184511/100000000000000 : ℝ)*(major1) + (1925789847184511/100000000000000 : ℝ)*(major2) + (693249076857769/25000000000000 : ℝ)*(sp0) + (69324870852767/2500000000000 : ℝ)*(sp1) + (1386497125120729/50000000000000 : ℝ)*(sp2) + (1078581942908747/100000000000000 : ℝ)*(sp3) + (230681833/100000000000000 : ℝ)*(sp4) + (7010529/800000000000 : ℝ)*(sp7) + (107858349237381/10000000000000 : ℝ)*(f.failure) + (693248966240993/25000000000000 : ℝ)*(f.sum) + (6890441023489/1910000000000000000000000000 : ℝ)*base65 + (1495454072493630753/191000000000000000000000000000000 : ℝ)*base68 + (27586960508369247/191000000000000000000000000000000 : ℝ)*base69 + (270108056677369247/191000000000000000000000000000000 : ℝ)*base71 + (799586723259/1910000000000000000000000000 : ℝ)*base73 + (203429492929369247/191000000000000000000000000000000 : ℝ)*base75 + (290665396227369247/191000000000000000000000000000000 : ℝ)*base77 + (352838869715369247/191000000000000000000000000000000 : ℝ)*base79 + (5394017183599/1910000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (168791/200000000000000000000 : ℝ)*base89 + (168791/200000000000000000000 : ℝ)*base91 + (168791/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (287098941190330984450961343/23875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (547663619/25000000000000 : ℝ)*(base19) + (26708211/1250000000000 : ℝ)*(base23) + (36170341/12500000000000 : ℝ)*(upper3) + (1726231/20000000000000 : ℝ)*(lower4) + (140600941/50000000000000 : ℝ)*(upper5) + (491575358853053/25000000000000 : ℝ)*(major0) + (491575358853053/25000000000000 : ℝ)*(major1) + (491575358853053/25000000000000 : ℝ)*(major2) + (9792277957/50000000000000 : ℝ)*(sp1) + (4128930207/20000000000000 : ℝ)*(sp2) + (1415664759169087/50000000000000 : ℝ)*(sp4) + (353913467890973/12500000000000 : ℝ)*(sp5) + (1415653368515129/50000000000000 : ℝ)*(sp6) + (550636475825013/50000000000000 : ℝ)*(sp7) + (550636475825013/50000000000000 : ℝ)*(f.failure) + (1415664759169087/50000000000000 : ℝ)*(f.sum) + (16309384983109/3342500000000000000000000000 : ℝ)*base65 + (3204055498838348533/334250000000000000000000000000000 : ℝ)*base68 + (1348527002758348533/334250000000000000000000000000000 : ℝ)*base70 + (95753276260151467/334250000000000000000000000000000 : ℝ)*base71 + (3947424508933/1671250000000000000000000000 : ℝ)*base74 + (1122082921321348533/334250000000000000000000000000000 : ℝ)*base76 + (1974051408783901467/334250000000000000000000000000000 : ℝ)*base77 + (3124733265592848533/334250000000000000000000000000000 : ℝ)*base80 + (56006516301/52226562500000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1700057/1000000000000000000000 : ℝ)*base90 + (1700057/1000000000000000000000 : ℝ)*base92 + (1700057/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1645_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35709611/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2933/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2373/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1211/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4337/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1645_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1645_s2_0 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-50600513/312500000 : ℝ)*x 0 + (5452892947/10000000000 : ℝ)*x 1 + (5180200949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50600513/312500000 : ℝ)^4899 ≤ (625514466559/6250000000000 : ℝ)^3875 := by
    have hnat : (50600513 : ℕ)^4899*6250000000000^3875 ≤ 625514466559^3875*312500000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50600513 312500000 625514466559 6250000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5452892947/10000000000 : ℝ)^4899 ≤ (46454578596651/100000000000000 : ℝ)^3875 := by
    have hnat : (5452892947 : ℕ)^4899*100000000000000^3875 ≤ 46454578596651^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452892947 10000000000 46454578596651 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5180200949/10000000000 : ℝ)^4899 ≤ (21768594961577/50000000000000 : ℝ)^3875 := by
    have hnat : (5180200949 : ℕ)^4899*50000000000000^3875 ≤ 21768594961577^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180200949 10000000000 21768594961577 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-50600513/312500000 : ℝ), (5452892947/10000000000 : ℝ), (5180200949/10000000000 : ℝ)] ![(625514466559/6250000000000 : ℝ), (46454578596651/100000000000000 : ℝ), (21768594961577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-50600513/312500000 : ℝ)|^4899 ≤ (625514466559/6250000000000 : ℝ)^3875
        have hw : |(-50600513/312500000 : ℝ)|=(50600513/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5452892947/10000000000 : ℝ)|^4899 ≤ (46454578596651/100000000000000 : ℝ)^3875
        have hw : |(5452892947/10000000000 : ℝ)|=(5452892947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5180200949/10000000000 : ℝ)|^4899 ≤ (21768594961577/50000000000000 : ℝ)^3875
        have hw : |(5180200949/10000000000 : ℝ)|=(5180200949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s2_1 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337384493/2500000000 : ℝ)*x 0 + (-1759734779/10000000000 : ℝ)*x 1 + (129505041/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337384493/2500000000 : ℝ)^4899 ≤ (22672095562993/50000000000000 : ℝ)^3875 := by
    have hnat : (1337384493 : ℕ)^4899*50000000000000^3875 ≤ 22672095562993^3875*2500000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337384493 2500000000 22672095562993 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1759734779/10000000000 : ℝ)^4899 ≤ (11118611599473/100000000000000 : ℝ)^3875 := by
    have hnat : (1759734779 : ℕ)^4899*100000000000000^3875 ≤ 11118611599473^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1759734779 10000000000 11118611599473 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (129505041/250000000 : ℝ)^4899 ≤ (43537197265377/100000000000000 : ℝ)^3875 := by
    have hnat : (129505041 : ℕ)^4899*100000000000000^3875 ≤ 43537197265377^3875*250000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129505041 250000000 43537197265377 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337384493/2500000000 : ℝ), (-1759734779/10000000000 : ℝ), (129505041/250000000 : ℝ)] ![(22672095562993/50000000000000 : ℝ), (11118611599473/100000000000000 : ℝ), (43537197265377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337384493/2500000000 : ℝ)|^4899 ≤ (22672095562993/50000000000000 : ℝ)^3875
        have hw : |(1337384493/2500000000 : ℝ)|=(1337384493/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1759734779/10000000000 : ℝ)|^4899 ≤ (11118611599473/100000000000000 : ℝ)^3875
        have hw : |(-1759734779/10000000000 : ℝ)|=(1759734779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(129505041/250000000 : ℝ)|^4899 ≤ (43537197265377/100000000000000 : ℝ)^3875
        have hw : |(129505041/250000000 : ℝ)|=(129505041/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s2_2 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349539903/10000000000 : ℝ)*x 0 + (5180200297/10000000000 : ℝ)*x 1 + (-879866987/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349539903/10000000000 : ℝ)^4899 ≤ (5668026477373/12500000000000 : ℝ)^3875 := by
    have hnat : (5349539903 : ℕ)^4899*12500000000000^3875 ≤ 5668026477373^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349539903 10000000000 5668026477373 12500000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180200297/10000000000 : ℝ)^4899 ≤ (21768591497663/50000000000000 : ℝ)^3875 := by
    have hnat : (5180200297 : ℕ)^4899*50000000000000^3875 ≤ 21768591497663^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180200297 10000000000 21768591497663 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (879866987/5000000000 : ℝ)^4899 ≤ (5559302584559/50000000000000 : ℝ)^3875 := by
    have hnat : (879866987 : ℕ)^4899*50000000000000^3875 ≤ 5559302584559^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879866987 5000000000 5559302584559 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349539903/10000000000 : ℝ), (5180200297/10000000000 : ℝ), (-879866987/5000000000 : ℝ)] ![(5668026477373/12500000000000 : ℝ), (21768591497663/50000000000000 : ℝ), (5559302584559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349539903/10000000000 : ℝ)|^4899 ≤ (5668026477373/12500000000000 : ℝ)^3875
        have hw : |(5349539903/10000000000 : ℝ)|=(5349539903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180200297/10000000000 : ℝ)|^4899 ≤ (21768591497663/50000000000000 : ℝ)^3875
        have hw : |(5180200297/10000000000 : ℝ)|=(5180200297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-879866987/5000000000 : ℝ)|^4899 ≤ (5559302584559/50000000000000 : ℝ)^3875
        have hw : |(-879866987/5000000000 : ℝ)|=(879866987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s2_3 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4184065547/10000000000 : ℝ)*x 0 + (192212579/500000000 : ℝ)*x 1 + (4545332277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4184065547/10000000000 : ℝ)^4899 ≤ (4154443328951/12500000000000 : ℝ)^3875 := by
    have hnat : (4184065547 : ℕ)^4899*12500000000000^3875 ≤ 4154443328951^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4184065547 10000000000 4154443328951 12500000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (192212579/500000000 : ℝ)^4899 ≤ (14930177678471/50000000000000 : ℝ)^3875 := by
    have hnat : (192212579 : ℕ)^4899*50000000000000^3875 ≤ 14930177678471^3875*500000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      192212579 500000000 14930177678471 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4545332277/10000000000 : ℝ)^4899 ≤ (4613012250087/12500000000000 : ℝ)^3875 := by
    have hnat : (4545332277 : ℕ)^4899*12500000000000^3875 ≤ 4613012250087^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4545332277 10000000000 4613012250087 12500000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4184065547/10000000000 : ℝ), (192212579/500000000 : ℝ), (4545332277/10000000000 : ℝ)] ![(4154443328951/12500000000000 : ℝ), (14930177678471/50000000000000 : ℝ), (4613012250087/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4184065547/10000000000 : ℝ)|^4899 ≤ (4154443328951/12500000000000 : ℝ)^3875
        have hw : |(4184065547/10000000000 : ℝ)|=(4184065547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(192212579/500000000 : ℝ)|^4899 ≤ (14930177678471/50000000000000 : ℝ)^3875
        have hw : |(192212579/500000000 : ℝ)|=(192212579/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4545332277/10000000000 : ℝ)|^4899 ≤ (4613012250087/12500000000000 : ℝ)^3875
        have hw : |(4545332277/10000000000 : ℝ)|=(4545332277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s2_4 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1619285703/10000000000 : ℝ)*x 0 + (5182316059/10000000000 : ℝ)*x 1 + (218030233/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1619285703/10000000000 : ℝ)^4899 ≤ (5004386447517/50000000000000 : ℝ)^3875 := by
    have hnat : (1619285703 : ℕ)^4899*50000000000000^3875 ≤ 5004386447517^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1619285703 10000000000 5004386447517 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182316059/10000000000 : ℝ)^4899 ≤ (21779832622131/50000000000000 : ℝ)^3875 := by
    have hnat : (5182316059 : ℕ)^4899*50000000000000^3875 ≤ 21779832622131^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182316059 10000000000 21779832622131 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (218030233/400000000 : ℝ)^4899 ≤ (5803945230117/12500000000000 : ℝ)^3875 := by
    have hnat : (218030233 : ℕ)^4899*12500000000000^3875 ≤ 5803945230117^3875*400000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      218030233 400000000 5803945230117 12500000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1619285703/10000000000 : ℝ), (5182316059/10000000000 : ℝ), (218030233/400000000 : ℝ)] ![(5004386447517/50000000000000 : ℝ), (21779832622131/50000000000000 : ℝ), (5803945230117/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1619285703/10000000000 : ℝ)|^4899 ≤ (5004386447517/50000000000000 : ℝ)^3875
        have hw : |(-1619285703/10000000000 : ℝ)|=(1619285703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182316059/10000000000 : ℝ)|^4899 ≤ (21779832622131/50000000000000 : ℝ)^3875
        have hw : |(5182316059/10000000000 : ℝ)|=(5182316059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(218030233/400000000 : ℝ)|^4899 ≤ (5803945230117/12500000000000 : ℝ)^3875
        have hw : |(218030233/400000000 : ℝ)|=(218030233/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s2_5 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276727823/10000000000 : ℝ)*x 0 + (-1489180067/10000000000 : ℝ)*x 1 + (5450755133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276727823/10000000000 : ℝ)^4899 ≤ (44565350326829/100000000000000 : ℝ)^3875 := by
    have hnat : (5276727823 : ℕ)^4899*100000000000000^3875 ≤ 44565350326829^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276727823 10000000000 44565350326829 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1489180067/10000000000 : ℝ)^4899 ≤ (4501547637721/50000000000000 : ℝ)^3875 := by
    have hnat : (1489180067 : ℕ)^4899*50000000000000^3875 ≤ 4501547637721^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1489180067 10000000000 4501547637721 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5450755133/10000000000 : ℝ)^4899 ≤ (23215777194249/50000000000000 : ℝ)^3875 := by
    have hnat : (5450755133 : ℕ)^4899*50000000000000^3875 ≤ 23215777194249^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450755133 10000000000 23215777194249 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276727823/10000000000 : ℝ), (-1489180067/10000000000 : ℝ), (5450755133/10000000000 : ℝ)] ![(44565350326829/100000000000000 : ℝ), (4501547637721/50000000000000 : ℝ), (23215777194249/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276727823/10000000000 : ℝ)|^4899 ≤ (44565350326829/100000000000000 : ℝ)^3875
        have hw : |(5276727823/10000000000 : ℝ)|=(5276727823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1489180067/10000000000 : ℝ)|^4899 ≤ (4501547637721/50000000000000 : ℝ)^3875
        have hw : |(-1489180067/10000000000 : ℝ)|=(1489180067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5450755133/10000000000 : ℝ)|^4899 ≤ (23215777194249/50000000000000 : ℝ)^3875
        have hw : |(5450755133/10000000000 : ℝ)|=(5450755133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s2_6 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (131918217/250000000 : ℝ)*x 0 + (1362688679/2500000000 : ℝ)*x 1 + (-1489179457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131918217/250000000 : ℝ)^4899 ≤ (44565359477421/100000000000000 : ℝ)^3875 := by
    have hnat : (131918217 : ℕ)^4899*100000000000000^3875 ≤ 44565359477421^3875*250000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131918217 250000000 44565359477421 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1362688679/2500000000 : ℝ)^4899 ≤ (928630997953/2000000000000 : ℝ)^3875 := by
    have hnat : (1362688679 : ℕ)^4899*2000000000000^3875 ≤ 928630997953^3875*2500000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362688679 2500000000 928630997953 2000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1489179457/10000000000 : ℝ)^4899 ≤ (1800618122607/20000000000000 : ℝ)^3875 := by
    have hnat : (1489179457 : ℕ)^4899*20000000000000^3875 ≤ 1800618122607^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1489179457 10000000000 1800618122607 20000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131918217/250000000 : ℝ), (1362688679/2500000000 : ℝ), (-1489179457/10000000000 : ℝ)] ![(44565359477421/100000000000000 : ℝ), (928630997953/2000000000000 : ℝ), (1800618122607/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131918217/250000000 : ℝ)|^4899 ≤ (44565359477421/100000000000000 : ℝ)^3875
        have hw : |(131918217/250000000 : ℝ)|=(131918217/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1362688679/2500000000 : ℝ)|^4899 ≤ (928630997953/2000000000000 : ℝ)^3875
        have hw : |(1362688679/2500000000 : ℝ)|=(1362688679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1489179457/10000000000 : ℝ)|^4899 ≤ (1800618122607/20000000000000 : ℝ)^3875
        have hw : |(-1489179457/10000000000 : ℝ)|=(1489179457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1645_s2_7 (p : ℝ) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2092123707/5000000000 : ℝ)*x 0 + (4539894291/10000000000 : ℝ)*x 1 + (1924873893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2092123707/5000000000 : ℝ)^4899 ≤ (16618686517019/50000000000000 : ℝ)^3875 := by
    have hnat : (2092123707 : ℕ)^4899*50000000000000^3875 ≤ 16618686517019^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092123707 5000000000 16618686517019 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4539894291/10000000000 : ℝ)^4899 ≤ (18424143866997/50000000000000 : ℝ)^3875 := by
    have hnat : (4539894291 : ℕ)^4899*50000000000000^3875 ≤ 18424143866997^3875*10000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4539894291 10000000000 18424143866997 50000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1924873893/5000000000 : ℝ)^4899 ≤ (29914339213857/100000000000000 : ℝ)^3875 := by
    have hnat : (1924873893 : ℕ)^4899*100000000000000^3875 ≤ 29914339213857^3875*5000000000^4899 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1924873893 5000000000 29914339213857 100000000000000 4899 3875 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4899/1024 : ℝ)) 4899 3875 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2092123707/5000000000 : ℝ), (4539894291/10000000000 : ℝ), (1924873893/5000000000 : ℝ)] ![(16618686517019/50000000000000 : ℝ), (18424143866997/50000000000000 : ℝ), (29914339213857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2092123707/5000000000 : ℝ)|^4899 ≤ (16618686517019/50000000000000 : ℝ)^3875
        have hw : |(2092123707/5000000000 : ℝ)|=(2092123707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4539894291/10000000000 : ℝ)|^4899 ≤ (18424143866997/50000000000000 : ℝ)^3875
        have hw : |(4539894291/10000000000 : ℝ)|=(4539894291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1924873893/5000000000 : ℝ)|^4899 ≤ (29914339213857/100000000000000 : ℝ)^3875
        have hw : |(1924873893/5000000000 : ℝ)|=(1924873893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1645_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35709611/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4337/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1211/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (1321/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8181/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4337/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1211/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4337/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1211/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4337/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1211/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4337/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1211/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4337/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1211/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4337/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1211/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1211/12500 : ℝ) ^ (4895/1024 : ℝ) ≤ (142535137966093/10000000000000000000 : ℝ) := by
    have hpowers : (1211/12500 : ℝ)^4895 ≤ (142535137966093/10000000000000000000 : ℝ)^1024 := by
      have hnat : (1211 : ℕ)^4895*10000000000000000000^1024 ≤ 142535137966093^1024*12500^4895 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1211 12500 142535137966093 10000000000000000000 4895 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1211/12500 : ℝ)) (X := (142535137966093/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4337/25000 : ℝ) ^ (4895/1024 : ℝ) ≤ (1154447487824919/5000000000000000000 : ℝ) := by
    have hpowers : (4337/25000 : ℝ)^4895 ≤ (1154447487824919/5000000000000000000 : ℝ)^1024 := by
      have hnat : (4337 : ℕ)^4895*5000000000000000000^1024 ≤ 1154447487824919^1024*25000^4895 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4337 25000 1154447487824919 5000000000000000000 4895 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4337/25000 : ℝ)) (X := (1154447487824919/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000142535137966093/5000000000000000000 : ℝ) ≤ (10000059634049489/10000000000000000 : ℝ) ^ (4895/1024 : ℝ) := by
    have hpowers : (5000142535137966093/5000000000000000000 : ℝ)^1024 ≤ (10000059634049489/10000000000000000 : ℝ)^4895 := by
      have hnat : (5000142535137966093 : ℕ)^1024*10000000000000000^4895 ≤ 10000059634049489^4895*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000142535137966093 5000000000000000000 10000059634049489 10000000000000000 1024 4895 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000059634049489/10000000000000000 : ℝ)) (X := (5000142535137966093/5000000000000000000 : ℝ)) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10002451430113615931/10000000000000000000 : ℝ) ≤ (1250064096556461/1250000000000000 : ℝ) ^ (4895/1024 : ℝ) := by
    have hpowers : (10002451430113615931/10000000000000000000 : ℝ)^1024 ≤ (1250064096556461/1250000000000000 : ℝ)^4895 := by
      have hnat : (10002451430113615931 : ℕ)^1024*1250000000000000^4895 ≤ 1250064096556461^4895*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002451430113615931 10000000000000000000 1250064096556461 1250000000000000 1024 4895 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250064096556461/1250000000000000 : ℝ)) (X := (10002451430113615931/10000000000000000000 : ℝ)) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501154447487824919/2500000000000000000 : ℝ) ≤ (10000965910853887/10000000000000000 : ℝ) ^ (4895/1024 : ℝ) := by
    have hpowers : (2501154447487824919/2500000000000000000 : ℝ)^1024 ≤ (10000965910853887/10000000000000000 : ℝ)^4895 := by
      have hnat : (2501154447487824919 : ℕ)^1024*10000000000000000^4895 ≤ 10000965910853887^4895*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501154447487824919 2500000000000000000 10000965910853887 10000000000000000 1024 4895 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000965910853887/10000000000000000 : ℝ)) (X := (2501154447487824919/2500000000000000000 : ℝ)) (by norm_num) 4895 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(142535137966093/10000000000000000000 : ℝ) ≤ ((19147919196784519479/19150000000000000000 : ℝ)+2*(453138402199/766000000000000 : ℝ)*(1211/12500 : ℝ))^(4895/1024 : ℝ) := by
    rw [show (19147919196784519479/19150000000000000000 : ℝ)+2*(453138402199/766000000000000 : ℝ)*(1211/12500 : ℝ)=(10000059634049489/10000000000000000 : ℝ) by norm_num, show 1+2*(142535137966093/10000000000000000000 : ℝ)=(5000142535137966093/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1154447487824919/5000000000000000000 : ℝ)+(142535137966093/10000000000000000000 : ℝ) ≤ ((19147919196784519479/19150000000000000000 : ℝ)+(453138402199/766000000000000 : ℝ)*((4337/25000 : ℝ)+(1211/12500 : ℝ)))^(4895/1024 : ℝ) := by
    rw [show (19147919196784519479/19150000000000000000 : ℝ)+(453138402199/766000000000000 : ℝ)*((4337/25000 : ℝ)+(1211/12500 : ℝ))=(1250064096556461/1250000000000000 : ℝ) by norm_num, show 1+(1154447487824919/5000000000000000000 : ℝ)+(142535137966093/10000000000000000000 : ℝ)=(10002451430113615931/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1154447487824919/5000000000000000000 : ℝ) ≤ ((19147919196784519479/19150000000000000000 : ℝ)+2*(453138402199/766000000000000 : ℝ)*(4337/25000 : ℝ))^(4895/1024 : ℝ) := by
    rw [show (19147919196784519479/19150000000000000000 : ℝ)+2*(453138402199/766000000000000 : ℝ)*(4337/25000 : ℝ)=(10000965910853887/10000000000000000 : ℝ) by norm_num, show 1+2*(1154447487824919/5000000000000000000 : ℝ)=(2501154447487824919/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19147919196784519479/19150000000000000000 : ℝ)*(X 1 0+X 2 0)+(453138402199/766000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4895/1024 : ℝ)) (lo := (1211/12500 : ℝ)) (hi := (4337/25000 : ℝ)) (c := (19147919196784519479/19150000000000000000 : ℝ)) (alpha := (453138402199/766000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19147919196784519479/19150000000000000000 : ℝ)*(X 0 1+X 2 1)+(453138402199/766000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4895/1024 : ℝ)) (lo := (1211/12500 : ℝ)) (hi := (4337/25000 : ℝ)) (c := (19147919196784519479/19150000000000000000 : ℝ)) (alpha := (453138402199/766000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19147919196784519479/19150000000000000000 : ℝ)*(X 0 2+X 1 2)+(453138402199/766000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4895/1024 : ℝ)) (lo := (1211/12500 : ℝ)) (hi := (4337/25000 : ℝ)) (c := (19147919196784519479/19150000000000000000 : ℝ)) (alpha := (453138402199/766000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-50600513/312500000 : ℝ)*X 0 0+(5452892947/10000000000 : ℝ)*X 0 1+(5180200949/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337384493/2500000000 : ℝ)*X 1 0+(-1759734779/10000000000 : ℝ)*X 1 1+(129505041/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349539903/10000000000 : ℝ)*X 2 0+(5180200297/10000000000 : ℝ)*X 2 1+(-879866987/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4184065547/10000000000 : ℝ)*X 0 0+(192212579/500000000 : ℝ)*X 0 1+(4545332277/10000000000 : ℝ)*X 0 2+(4184065547/10000000000 : ℝ)*X 1 0+(192212579/500000000 : ℝ)*X 1 1+(4545332277/10000000000 : ℝ)*X 1 2+(4184065547/10000000000 : ℝ)*X 2 0+(192212579/500000000 : ℝ)*X 2 1+(4545332277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1619285703/10000000000 : ℝ)*X 0 0+(5182316059/10000000000 : ℝ)*X 0 1+(218030233/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5276727823/10000000000 : ℝ)*X 1 0+(-1489180067/10000000000 : ℝ)*X 1 1+(5450755133/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((131918217/250000000 : ℝ)*X 2 0+(1362688679/2500000000 : ℝ)*X 2 1+(-1489179457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2092123707/5000000000 : ℝ)*X 0 0+(4539894291/10000000000 : ℝ)*X 0 1+(1924873893/5000000000 : ℝ)*X 0 2+(2092123707/5000000000 : ℝ)*X 1 0+(4539894291/10000000000 : ℝ)*X 1 1+(1924873893/5000000000 : ℝ)*X 1 2+(2092123707/5000000000 : ℝ)*X 2 0+(4539894291/10000000000 : ℝ)*X 2 1+(1924873893/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1645_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3336015068965466646002487207/478750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (158898897/25000000000000 : ℝ)*(base19) + (1081/64000000 : ℝ)*(base23) + (81715107/50000000000000 : ℝ)*(upper4) + (92932589/20000000000000 : ℝ)*(upper5) + (1273387171961211/50000000000000 : ℝ)*(major0) + (1273387171961211/50000000000000 : ℝ)*(major1) + (1273387171961211/50000000000000 : ℝ)*(major2) + (916786210649157/25000000000000 : ℝ)*(sp0) + (1833582447893953/50000000000000 : ℝ)*(sp1) + (1833583216069233/50000000000000 : ℝ)*(sp2) + (1426375175197659/100000000000000 : ℝ)*(sp3) + (11639302169/50000000000000 : ℝ)*(sp4) + (258981747/10000000000000 : ℝ)*(sp5) + (644896703/12500000000000 : ℝ)*(sp7) + (1426380334371283/100000000000000 : ℝ)*(f.failure) + (733433624240193/20000000000000 : ℝ)*(f.sum) + (12712316582061/19150000000000000000000000000 : ℝ)*base66 + (5818487851128345931/957500000000000000000000000000000 : ℝ)*base68 + (1664303597530845931/957500000000000000000000000000000 : ℝ)*base70 + (1769908591595845931/957500000000000000000000000000000 : ℝ)*base72 + (106841088938011/19150000000000000000000000000 : ℝ)*base74 + (11094029121909154069/957500000000000000000000000000000 : ℝ)*base75 + (852982037465845931/957500000000000000000000000000000 : ℝ)*base78 + (1835118208991654069/957500000000000000000000000000000 : ℝ)*base79 + (7039209052461/19150000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (5500913/2000000000000000000000 : ℝ)*base89 + (5500913/2000000000000000000000 : ℝ)*base91 + (5500913/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1150699674014853757919066397/239375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (75612581/25000000000000 : ℝ)*(base19) + (10760923/800000000000 : ℝ)*(base23) + (111510961/100000000000000 : ℝ)*(lower2) + (251184933/100000000000000 : ℝ)*(lower4) + (1476723/12500000000000 : ℝ)*(upper5) + (646776119696973/25000000000000 : ℝ)*(major0) + (646776119696973/25000000000000 : ℝ)*(major1) + (646776119696973/25000000000000 : ℝ)*(major2) + (555315219/12500000000000 : ℝ)*(sp0) + (6266821639/50000000000000 : ℝ)*(sp2) + (1862618094177437/50000000000000 : ℝ)*(sp4) + (1862620164213151/50000000000000 : ℝ)*(sp5) + (1862613376058987/50000000000000 : ℝ)*(sp6) + (1415007975061/97656250000 : ℝ)*(sp7) + (1415007975061/97656250000 : ℝ)*(f.failure) + (3725240630876627/100000000000000 : ℝ)*(f.sum) + (35898627281477/9575000000000000000000000000 : ℝ)*base65 + (7417040274834012067/478750000000000000000000000000000 : ℝ)*base67 + (4813937367529012067/478750000000000000000000000000000 : ℝ)*base69 + (5312325577629012067/478750000000000000000000000000000 : ℝ)*base71 + (27506619029377/9575000000000000000000000000 : ℝ)*base73 + (10007166278474012067/478750000000000000000000000000000 : ℝ)*base75 + (3296972009549012067/478750000000000000000000000000000 : ℝ)*base77 + (2504819082434012067/478750000000000000000000000000000 : ℝ)*base79 + (5876243774577/9575000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (2177/976562500000000000 : ℝ)*base90 + (2177/976562500000000000 : ℝ)*base92 + (2177/976562500000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1645_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35709611/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4337/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1211/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1321/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8181/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1645_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1645_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35709611/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1321/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8181/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1645_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1645_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1645_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4895/1024 : ℝ) ≤ p) (hpb : p ≤ (4899/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35709611/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1321/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8181/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1645_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
