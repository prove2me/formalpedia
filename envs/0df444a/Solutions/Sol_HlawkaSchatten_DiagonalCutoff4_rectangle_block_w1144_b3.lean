-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1144_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:33:24.059584+00:00
-- url     : https://prove2.me/submissions/e9a170a2-70bf-4450-aa88-719632b7db85

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
theorem support_rectangle_w1144_s9_0 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-541483501/2500000000 : ℝ)*x 0 + (674118431/1250000000 : ℝ)*x 1 + (5265819469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541483501/2500000000 : ℝ)^8337 ≤ (6580659911813/50000000000000 : ℝ)^6289 := by
    have hnat : (541483501 : ℕ)^8337*50000000000000^6289 ≤ 6580659911813^6289*2500000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541483501 2500000000 6580659911813 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674118431/1250000000 : ℝ)^8337 ≤ (11026455856011/25000000000000 : ℝ)^6289 := by
    have hnat : (674118431 : ℕ)^8337*25000000000000^6289 ≤ 11026455856011^6289*1250000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674118431 1250000000 11026455856011 25000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265819469/10000000000 : ℝ)^8337 ≤ (5341607091269/12500000000000 : ℝ)^6289 := by
    have hnat : (5265819469 : ℕ)^8337*12500000000000^6289 ≤ 5341607091269^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265819469 10000000000 5341607091269 12500000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-541483501/2500000000 : ℝ), (674118431/1250000000 : ℝ), (5265819469/10000000000 : ℝ)] ![(6580659911813/50000000000000 : ℝ), (11026455856011/25000000000000 : ℝ), (5341607091269/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-541483501/2500000000 : ℝ)|^8337 ≤ (6580659911813/50000000000000 : ℝ)^6289
        have hw : |(-541483501/2500000000 : ℝ)|=(541483501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674118431/1250000000 : ℝ)|^8337 ≤ (11026455856011/25000000000000 : ℝ)^6289
        have hw : |(674118431/1250000000 : ℝ)|=(674118431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265819469/10000000000 : ℝ)|^8337 ≤ (5341607091269/12500000000000 : ℝ)^6289
        have hw : |(5265819469/10000000000 : ℝ)|=(5265819469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s9_1 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344738097/10000000000 : ℝ)*x 0 + (-1115207137/5000000000 : ℝ)*x 1 + (1053163891/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344738097/10000000000 : ℝ)^8337 ≤ (21791956861997/50000000000000 : ℝ)^6289 := by
    have hnat : (5344738097 : ℕ)^8337*50000000000000^6289 ≤ 21791956861997^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344738097 10000000000 21791956861997 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1115207137/5000000000 : ℝ)^8337 ≤ (2736645936301/20000000000000 : ℝ)^6289 := by
    have hnat : (1115207137 : ℕ)^8337*20000000000000^6289 ≤ 2736645936301^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1115207137 5000000000 2736645936301 20000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053163891/2000000000 : ℝ)^8337 ≤ (21366428289771/50000000000000 : ℝ)^6289 := by
    have hnat : (1053163891 : ℕ)^8337*50000000000000^6289 ≤ 21366428289771^6289*2000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053163891 2000000000 21366428289771 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344738097/10000000000 : ℝ), (-1115207137/5000000000 : ℝ), (1053163891/2000000000 : ℝ)] ![(21791956861997/50000000000000 : ℝ), (2736645936301/20000000000000 : ℝ), (21366428289771/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344738097/10000000000 : ℝ)|^8337 ≤ (21791956861997/50000000000000 : ℝ)^6289
        have hw : |(5344738097/10000000000 : ℝ)|=(5344738097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1115207137/5000000000 : ℝ)|^8337 ≤ (2736645936301/20000000000000 : ℝ)^6289
        have hw : |(-1115207137/5000000000 : ℝ)|=(1115207137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053163891/2000000000 : ℝ)|^8337 ≤ (21366428289771/50000000000000 : ℝ)^6289
        have hw : |(1053163891/2000000000 : ℝ)|=(1053163891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s9_2 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672369019/5000000000 : ℝ)*x 0 + (1053163893/2000000000 : ℝ)*x 1 + (-2230414339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672369019/5000000000 : ℝ)^8337 ≤ (217919565431/500000000000 : ℝ)^6289 := by
    have hnat : (2672369019 : ℕ)^8337*500000000000^6289 ≤ 217919565431^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672369019 5000000000 217919565431 500000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053163893/2000000000 : ℝ)^8337 ≤ (534160708589/1250000000000 : ℝ)^6289 := by
    have hnat : (1053163893 : ℕ)^8337*1250000000000^6289 ≤ 534160708589^6289*2000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053163893 2000000000 534160708589 1250000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2230414339/10000000000 : ℝ)^8337 ≤ (13683230210127/100000000000000 : ℝ)^6289 := by
    have hnat : (2230414339 : ℕ)^8337*100000000000000^6289 ≤ 13683230210127^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2230414339 10000000000 13683230210127 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672369019/5000000000 : ℝ), (1053163893/2000000000 : ℝ), (-2230414339/10000000000 : ℝ)] ![(217919565431/500000000000 : ℝ), (534160708589/1250000000000 : ℝ), (13683230210127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672369019/5000000000 : ℝ)|^8337 ≤ (217919565431/500000000000 : ℝ)^6289
        have hw : |(2672369019/5000000000 : ℝ)|=(2672369019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053163893/2000000000 : ℝ)|^8337 ≤ (534160708589/1250000000000 : ℝ)^6289
        have hw : |(1053163893/2000000000 : ℝ)|=(1053163893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2230414339/10000000000 : ℝ)|^8337 ≤ (13683230210127/100000000000000 : ℝ)^6289
        have hw : |(-2230414339/10000000000 : ℝ)|=(2230414339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s9_3 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4364393939/10000000000 : ℝ)*x 0 + (26498181/62500000 : ℝ)*x 1 + (1123181557/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364393939/10000000000 : ℝ)^8337 ≤ (33317001782431/100000000000000 : ℝ)^6289 := by
    have hnat : (4364393939 : ℕ)^8337*100000000000000^6289 ≤ 33317001782431^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364393939 10000000000 33317001782431 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26498181/62500000 : ℝ)^8337 ≤ (32061127368223/100000000000000 : ℝ)^6289 := by
    have hnat : (26498181 : ℕ)^8337*100000000000000^6289 ≤ 32061127368223^6289*62500000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26498181 62500000 32061127368223 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123181557/2500000000 : ℝ)^8337 ≤ (34621870830297/100000000000000 : ℝ)^6289 := by
    have hnat : (1123181557 : ℕ)^8337*100000000000000^6289 ≤ 34621870830297^6289*2500000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123181557 2500000000 34621870830297 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364393939/10000000000 : ℝ), (26498181/62500000 : ℝ), (1123181557/2500000000 : ℝ)] ![(33317001782431/100000000000000 : ℝ), (32061127368223/100000000000000 : ℝ), (34621870830297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364393939/10000000000 : ℝ)|^8337 ≤ (33317001782431/100000000000000 : ℝ)^6289
        have hw : |(4364393939/10000000000 : ℝ)|=(4364393939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(26498181/62500000 : ℝ)|^8337 ≤ (32061127368223/100000000000000 : ℝ)^6289
        have hw : |(26498181/62500000 : ℝ)|=(26498181/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1123181557/2500000000 : ℝ)|^8337 ≤ (34621870830297/100000000000000 : ℝ)^6289
        have hw : |(1123181557/2500000000 : ℝ)|=(1123181557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s9_4 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1082969553/5000000000 : ℝ)*x 0 + (1316534657/2500000000 : ℝ)*x 1 + (2696313481/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082969553/5000000000 : ℝ)^8337 ≤ (13161360921849/100000000000000 : ℝ)^6289 := by
    have hnat : (1082969553 : ℕ)^8337*100000000000000^6289 ≤ 13161360921849^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082969553 5000000000 13161360921849 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316534657/2500000000 : ℝ)^8337 ≤ (1335509069321/3125000000000 : ℝ)^6289 := by
    have hnat : (1316534657 : ℕ)^8337*3125000000000^6289 ≤ 1335509069321^6289*2500000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316534657 2500000000 1335509069321 3125000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696313481/5000000000 : ℝ)^8337 ≤ (22051174420031/50000000000000 : ℝ)^6289 := by
    have hnat : (2696313481 : ℕ)^8337*50000000000000^6289 ≤ 22051174420031^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696313481 5000000000 22051174420031 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1082969553/5000000000 : ℝ), (1316534657/2500000000 : ℝ), (2696313481/5000000000 : ℝ)] ![(13161360921849/100000000000000 : ℝ), (1335509069321/3125000000000 : ℝ), (22051174420031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1082969553/5000000000 : ℝ)|^8337 ≤ (13161360921849/100000000000000 : ℝ)^6289
        have hw : |(-1082969553/5000000000 : ℝ)|=(1082969553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316534657/2500000000 : ℝ)|^8337 ≤ (1335509069321/3125000000000 : ℝ)^6289
        have hw : |(1316534657/2500000000 : ℝ)|=(1316534657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696313481/5000000000 : ℝ)|^8337 ≤ (22051174420031/50000000000000 : ℝ)^6289
        have hw : |(2696313481/5000000000 : ℝ)|=(2696313481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s9_5 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4364403669/10000000000 : ℝ)*x 0 + (4492090897/10000000000 : ℝ)*x 1 + (848069309/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364403669/10000000000 : ℝ)^8337 ≤ (33317100247723/100000000000000 : ℝ)^6289 := by
    have hnat : (4364403669 : ℕ)^8337*100000000000000^6289 ≤ 33317100247723^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364403669 10000000000 33317100247723 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4492090897/10000000000 : ℝ)^8337 ≤ (8653845154773/25000000000000 : ℝ)^6289 := by
    have hnat : (4492090897 : ℕ)^8337*25000000000000^6289 ≤ 8653845154773^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492090897 10000000000 8653845154773 25000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (848069309/2000000000 : ℝ)^8337 ≤ (8016879779173/25000000000000 : ℝ)^6289 := by
    have hnat : (848069309 : ℕ)^8337*25000000000000^6289 ≤ 8016879779173^6289*2000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848069309 2000000000 8016879779173 25000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364403669/10000000000 : ℝ), (4492090897/10000000000 : ℝ), (848069309/2000000000 : ℝ)] ![(33317100247723/100000000000000 : ℝ), (8653845154773/25000000000000 : ℝ), (8016879779173/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364403669/10000000000 : ℝ)|^8337 ≤ (33317100247723/100000000000000 : ℝ)^6289
        have hw : |(4364403669/10000000000 : ℝ)|=(4364403669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4492090897/10000000000 : ℝ)|^8337 ≤ (8653845154773/25000000000000 : ℝ)^6289
        have hw : |(4492090897/10000000000 : ℝ)|=(4492090897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(848069309/2000000000 : ℝ)|^8337 ≤ (8016879779173/25000000000000 : ℝ)^6289
        have hw : |(848069309/2000000000 : ℝ)|=(848069309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1144_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37378183/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (281/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2839/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11357/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (281/2000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (281/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2839/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (281/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2839/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (281/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2839/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (281/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2839/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (281/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2839/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (281/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2839/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2839/25000 : ℝ) ^ (521/128 : ℝ) ≤ (7135790228397217/50000000000000000000 : ℝ) := by
    have hpowers : (2839/25000 : ℝ)^521 ≤ (7135790228397217/50000000000000000000 : ℝ)^128 := by
      have hnat : (2839 : ℕ)^521*50000000000000000000^128 ≤ 7135790228397217^128*25000^521 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2839 25000 7135790228397217 50000000000000000000 521 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2839/25000 : ℝ)) (X := (7135790228397217/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hpowhi : (281/2000 : ℝ) ^ (521/128 : ℝ) ≤ (1060782411433317/3125000000000000000 : ℝ) := by
    have hpowers : (281/2000 : ℝ)^521 ≤ (1060782411433317/3125000000000000000 : ℝ)^128 := by
      have hnat : (281 : ℕ)^521*3125000000000000000^128 ≤ 1060782411433317^128*2000^521 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        281 2000 1060782411433317 3125000000000000000 521 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (281/2000 : ℝ)) (X := (1060782411433317/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25007135790228397217/25000000000000000000 : ℝ) ≤ (500035058842121/500000000000000 : ℝ) ^ (521/128 : ℝ) := by
    have hpowers : (25007135790228397217/25000000000000000000 : ℝ)^128 ≤ (500035058842121/500000000000000 : ℝ)^521 := by
      have hnat : (25007135790228397217 : ℕ)^128*500000000000000^521 ≤ 500035058842121^521*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25007135790228397217 25000000000000000000 500035058842121 500000000000000 128 521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500035058842121/500000000000000 : ℝ)) (X := (25007135790228397217/25000000000000000000 : ℝ)) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024108308811330289/50000000000000000000 : ℝ) ≤ (2000236875432711/2000000000000000 : ℝ) ^ (521/128 : ℝ) := by
    have hpowers : (50024108308811330289/50000000000000000000 : ℝ)^128 ≤ (2000236875432711/2000000000000000 : ℝ)^521 := by
      have hnat : (50024108308811330289 : ℕ)^128*2000000000000000^521 ≤ 2000236875432711^521*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024108308811330289 50000000000000000000 2000236875432711 2000000000000000 128 521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000236875432711/2000000000000000 : ℝ)) (X := (50024108308811330289/50000000000000000000 : ℝ)) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563560782411433317/1562500000000000000 : ℝ) ≤ (1000166757748469/1000000000000000 : ℝ) ^ (521/128 : ℝ) := by
    have hpowers : (1563560782411433317/1562500000000000000 : ℝ)^128 ≤ (1000166757748469/1000000000000000 : ℝ)^521 := by
      have hnat : (1563560782411433317 : ℕ)^128*1000000000000000^521 ≤ 1000166757748469^521*1562500000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563560782411433317 1562500000000000000 1000166757748469 1000000000000000 128 521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000166757748469/1000000000000000 : ℝ)) (X := (1563560782411433317/1562500000000000000 : ℝ)) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(7135790228397217/50000000000000000000 : ℝ) ≤ ((336636431558998267/336750000000000000 : ℝ)+2*(96640064227/53880000000000 : ℝ)*(2839/25000 : ℝ))^(521/128 : ℝ) := by
    rw [show (336636431558998267/336750000000000000 : ℝ)+2*(96640064227/53880000000000 : ℝ)*(2839/25000 : ℝ)=(500035058842121/500000000000000 : ℝ) by norm_num, show 1+2*(7135790228397217/50000000000000000000 : ℝ)=(25007135790228397217/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1060782411433317/3125000000000000000 : ℝ)+(7135790228397217/50000000000000000000 : ℝ) ≤ ((336636431558998267/336750000000000000 : ℝ)+(96640064227/53880000000000 : ℝ)*((281/2000 : ℝ)+(2839/25000 : ℝ)))^(521/128 : ℝ) := by
    rw [show (336636431558998267/336750000000000000 : ℝ)+(96640064227/53880000000000 : ℝ)*((281/2000 : ℝ)+(2839/25000 : ℝ))=(2000236875432711/2000000000000000 : ℝ) by norm_num, show 1+(1060782411433317/3125000000000000000 : ℝ)+(7135790228397217/50000000000000000000 : ℝ)=(50024108308811330289/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1060782411433317/3125000000000000000 : ℝ) ≤ ((336636431558998267/336750000000000000 : ℝ)+2*(96640064227/53880000000000 : ℝ)*(281/2000 : ℝ))^(521/128 : ℝ) := by
    rw [show (336636431558998267/336750000000000000 : ℝ)+2*(96640064227/53880000000000 : ℝ)*(281/2000 : ℝ)=(1000166757748469/1000000000000000 : ℝ) by norm_num, show 1+2*(1060782411433317/3125000000000000000 : ℝ)=(1563560782411433317/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (336636431558998267/336750000000000000 : ℝ)*(X 1 0+X 2 0)+(96640064227/53880000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (521/128 : ℝ)) (lo := (2839/25000 : ℝ)) (hi := (281/2000 : ℝ)) (c := (336636431558998267/336750000000000000 : ℝ)) (alpha := (96640064227/53880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (336636431558998267/336750000000000000 : ℝ)*(X 0 1+X 2 1)+(96640064227/53880000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (521/128 : ℝ)) (lo := (2839/25000 : ℝ)) (hi := (281/2000 : ℝ)) (c := (336636431558998267/336750000000000000 : ℝ)) (alpha := (96640064227/53880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (336636431558998267/336750000000000000 : ℝ)*(X 0 2+X 1 2)+(96640064227/53880000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (521/128 : ℝ)) (lo := (2839/25000 : ℝ)) (hi := (281/2000 : ℝ)) (c := (336636431558998267/336750000000000000 : ℝ)) (alpha := (96640064227/53880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-541483501/2500000000 : ℝ)*X 0 0+(674118431/1250000000 : ℝ)*X 0 1+(5265819469/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s9_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344738097/10000000000 : ℝ)*X 1 0+(-1115207137/5000000000 : ℝ)*X 1 1+(1053163891/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s9_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672369019/5000000000 : ℝ)*X 2 0+(1053163893/2000000000 : ℝ)*X 2 1+(-2230414339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s9_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4364393939/10000000000 : ℝ)*X 0 0+(26498181/62500000 : ℝ)*X 0 1+(1123181557/2500000000 : ℝ)*X 0 2+(4364393939/10000000000 : ℝ)*X 1 0+(26498181/62500000 : ℝ)*X 1 1+(1123181557/2500000000 : ℝ)*X 1 2+(4364393939/10000000000 : ℝ)*X 2 0+(26498181/62500000 : ℝ)*X 2 1+(1123181557/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s9_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1082969553/5000000000 : ℝ)*X 0 0+(1316534657/2500000000 : ℝ)*X 0 1+(2696313481/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s9_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4364403669/10000000000 : ℝ)*X 0 0+(4492090897/10000000000 : ℝ)*X 0 1+(848069309/2000000000 : ℝ)*X 0 2+(4364403669/10000000000 : ℝ)*X 1 0+(4492090897/10000000000 : ℝ)*X 1 1+(848069309/2000000000 : ℝ)*X 1 2+(4364403669/10000000000 : ℝ)*X 2 0+(4492090897/10000000000 : ℝ)*X 2 1+(848069309/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1851583921516497986731599/701562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (572358461/100000000000000 : ℝ)*(base19) + (49842959/10000000000000 : ℝ)*(base23) + (12600171/100000000000000 : ℝ)*(lower2) + (22230447/20000000000000 : ℝ)*(upper3) + (779889/4000000000000 : ℝ)*(lower4) + (5909218536745087/100000000000000 : ℝ)*(major0) + (5909218536745087/100000000000000 : ℝ)*(major1) + (5909218536745087/100000000000000 : ℝ)*(major2) + (7866107306292169/100000000000000 : ℝ)*(sp0) + (1966529617064547/25000000000000 : ℝ)*(sp1) + (3933059271093529/50000000000000 : ℝ)*(sp2) + (98807694838407/2500000000000 : ℝ)*(sp3) + (9167441/78125000000 : ℝ)*(sp4) + (5075681473/50000000000000 : ℝ)*(sp5) + (1976158972449613/50000000000000 : ℝ)*(f.failure) + (983264880077081/12500000000000 : ℝ)*(f.sum) + (5596450982423/2694000000000000000000000000 : ℝ)*base66 + (289022158711995479/33675000000000000000000000000000 : ℝ)*base67 + (214047400657020479/33675000000000000000000000000000 : ℝ)*base69 + (414659390635695479/33675000000000000000000000000000 : ℝ)*base71 + (8203107082849/2694000000000000000000000000 : ℝ)*base73 + (48825070354695479/33675000000000000000000000000000 : ℝ)*base75 + (617782816013295479/33675000000000000000000000000000 : ℝ)*base77 + (11444234959154521/33675000000000000000000000000000 : ℝ)*base80 + (15277939424363/2694000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (5493179/1250000000000000000000 : ℝ)*base89 + (5493179/1250000000000000000000 : ℝ)*base91 + (5493179/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1144_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37378183/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (281/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2839/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11357/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (281/2000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1144_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1144_s10_0 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2165931337/10000000000 : ℝ)*x 0 + (2696472091/5000000000 : ℝ)*x 1 + (2632912379/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2165931337/10000000000 : ℝ)^8337 ≤ (1316129834011/10000000000000 : ℝ)^6289 := by
    have hnat : (2165931337 : ℕ)^8337*10000000000000^6289 ≤ 1316129834011^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165931337 10000000000 1316129834011 10000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696472091/5000000000 : ℝ)^8337 ≤ (44105788015009/100000000000000 : ℝ)^6289 := by
    have hnat : (2696472091 : ℕ)^8337*100000000000000^6289 ≤ 44105788015009^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696472091 5000000000 44105788015009 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632912379/5000000000 : ℝ)^8337 ≤ (42732913628257/100000000000000 : ℝ)^6289 := by
    have hnat : (2632912379 : ℕ)^8337*100000000000000^6289 ≤ 42732913628257^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632912379 5000000000 42732913628257 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2165931337/10000000000 : ℝ), (2696472091/5000000000 : ℝ), (2632912379/5000000000 : ℝ)] ![(1316129834011/10000000000000 : ℝ), (44105788015009/100000000000000 : ℝ), (42732913628257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2165931337/10000000000 : ℝ)|^8337 ≤ (1316129834011/10000000000000 : ℝ)^6289
        have hw : |(-2165931337/10000000000 : ℝ)|=(2165931337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696472091/5000000000 : ℝ)|^8337 ≤ (44105788015009/100000000000000 : ℝ)^6289
        have hw : |(2696472091/5000000000 : ℝ)|=(2696472091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632912379/5000000000 : ℝ)|^8337 ≤ (42732913628257/100000000000000 : ℝ)^6289
        have hw : |(2632912379/5000000000 : ℝ)|=(2632912379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s10_1 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344738699/10000000000 : ℝ)*x 0 + (-557601567/2500000000 : ℝ)*x 1 + (2632912451/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344738699/10000000000 : ℝ)^8337 ≤ (1361997507239/3125000000000 : ℝ)^6289 := by
    have hnat : (5344738699 : ℕ)^8337*3125000000000^6289 ≤ 1361997507239^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344738699 10000000000 1361997507239 3125000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (557601567/2500000000 : ℝ)^8337 ≤ (6841582285833/50000000000000 : ℝ)^6289 := by
    have hnat : (557601567 : ℕ)^8337*50000000000000^6289 ≤ 6841582285833^6289*2500000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      557601567 2500000000 6841582285833 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632912451/5000000000 : ℝ)^8337 ≤ (42732915177383/100000000000000 : ℝ)^6289 := by
    have hnat : (2632912451 : ℕ)^8337*100000000000000^6289 ≤ 42732915177383^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632912451 5000000000 42732915177383 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344738699/10000000000 : ℝ), (-557601567/2500000000 : ℝ), (2632912451/5000000000 : ℝ)] ![(1361997507239/3125000000000 : ℝ), (6841582285833/50000000000000 : ℝ), (42732915177383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344738699/10000000000 : ℝ)|^8337 ≤ (1361997507239/3125000000000 : ℝ)^6289
        have hw : |(5344738699/10000000000 : ℝ)|=(5344738699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-557601567/2500000000 : ℝ)|^8337 ≤ (6841582285833/50000000000000 : ℝ)^6289
        have hw : |(-557601567/2500000000 : ℝ)|=(557601567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632912451/5000000000 : ℝ)|^8337 ≤ (42732915177383/100000000000000 : ℝ)^6289
        have hw : |(2632912451/5000000000 : ℝ)|=(2632912451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s10_2 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-108296803/500000000 : ℝ)*x 0 + (2633072017/5000000000 : ℝ)*x 1 + (5392623861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108296803/500000000 : ℝ)^8337 ≤ (1645167048169/12500000000000 : ℝ)^6289 := by
    have hnat : (108296803 : ℕ)^8337*12500000000000^6289 ≤ 1645167048169^6289*500000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108296803 500000000 1645167048169 12500000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633072017/5000000000 : ℝ)^8337 ≤ (42736348376191/100000000000000 : ℝ)^6289 := by
    have hnat : (2633072017 : ℕ)^8337*100000000000000^6289 ≤ 42736348376191^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633072017 5000000000 42736348376191 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392623861/10000000000 : ℝ)^8337 ≤ (551278940257/1250000000000 : ℝ)^6289 := by
    have hnat : (5392623861 : ℕ)^8337*1250000000000^6289 ≤ 551278940257^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392623861 10000000000 551278940257 1250000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-108296803/500000000 : ℝ), (2633072017/5000000000 : ℝ), (5392623861/10000000000 : ℝ)] ![(1645167048169/12500000000000 : ℝ), (42736348376191/100000000000000 : ℝ), (551278940257/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-108296803/500000000 : ℝ)|^8337 ≤ (1645167048169/12500000000000 : ℝ)^6289
        have hw : |(-108296803/500000000 : ℝ)|=(108296803/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633072017/5000000000 : ℝ)|^8337 ≤ (42736348376191/100000000000000 : ℝ)^6289
        have hw : |(2633072017/5000000000 : ℝ)|=(2633072017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392623861/10000000000 : ℝ)|^8337 ≤ (551278940257/1250000000000 : ℝ)^6289
        have hw : |(5392623861/10000000000 : ℝ)|=(5392623861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s10_3 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062505463/2000000000 : ℝ)*x 0 + (-13147551/62500000 : ℝ)*x 1 + (5392623489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062505463/2000000000 : ℝ)^8337 ≤ (21618027732323/50000000000000 : ℝ)^6289 := by
    have hnat : (1062505463 : ℕ)^8337*50000000000000^6289 ≤ 21618027732323^6289*2000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062505463 2000000000 21618027732323 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (13147551/62500000 : ℝ)^8337 ≤ (791352083001/6250000000000 : ℝ)^6289 := by
    have hnat : (13147551 : ℕ)^8337*6250000000000^6289 ≤ 791352083001^6289*62500000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13147551 62500000 791352083001 6250000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392623489/10000000000 : ℝ)^8337 ≤ (44102311187521/100000000000000 : ℝ)^6289 := by
    have hnat : (5392623489 : ℕ)^8337*100000000000000^6289 ≤ 44102311187521^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392623489 10000000000 44102311187521 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062505463/2000000000 : ℝ), (-13147551/62500000 : ℝ), (5392623489/10000000000 : ℝ)] ![(21618027732323/50000000000000 : ℝ), (791352083001/6250000000000 : ℝ), (44102311187521/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062505463/2000000000 : ℝ)|^8337 ≤ (21618027732323/50000000000000 : ℝ)^6289
        have hw : |(1062505463/2000000000 : ℝ)|=(1062505463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-13147551/62500000 : ℝ)|^8337 ≤ (791352083001/6250000000000 : ℝ)^6289
        have hw : |(-13147551/62500000 : ℝ)|=(13147551/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392623489/10000000000 : ℝ)|^8337 ≤ (44102311187521/100000000000000 : ℝ)^6289
        have hw : |(5392623489/10000000000 : ℝ)|=(5392623489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s10_4 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312526973/10000000000 : ℝ)*x 0 + (337038993/625000000 : ℝ)*x 1 + (-26295101/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312526973/10000000000 : ℝ)^8337 ≤ (43236051774877/100000000000000 : ℝ)^6289 := by
    have hnat : (5312526973 : ℕ)^8337*100000000000000^6289 ≤ 43236051774877^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312526973 10000000000 43236051774877 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337038993/625000000 : ℝ)^8337 ≤ (137819735979/312500000000 : ℝ)^6289 := by
    have hnat : (337038993 : ℕ)^8337*312500000000^6289 ≤ 137819735979^6289*625000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337038993 625000000 137819735979 312500000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26295101/125000000 : ℝ)^8337 ≤ (12661632689689/100000000000000 : ℝ)^6289 := by
    have hnat : (26295101 : ℕ)^8337*100000000000000^6289 ≤ 12661632689689^6289*125000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26295101 125000000 12661632689689 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312526973/10000000000 : ℝ), (337038993/625000000 : ℝ), (-26295101/125000000 : ℝ)] ![(43236051774877/100000000000000 : ℝ), (137819735979/312500000000 : ℝ), (12661632689689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312526973/10000000000 : ℝ)|^8337 ≤ (43236051774877/100000000000000 : ℝ)^6289
        have hw : |(5312526973/10000000000 : ℝ)|=(5312526973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337038993/625000000 : ℝ)|^8337 ≤ (137819735979/312500000000 : ℝ)^6289
        have hw : |(337038993/625000000 : ℝ)|=(337038993/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-26295101/125000000 : ℝ)|^8337 ≤ (12661632689689/100000000000000 : ℝ)^6289
        have hw : |(-26295101/125000000 : ℝ)|=(26295101/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_s10_5 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (87288079/200000000 : ℝ)*x 0 + (280755113/625000000 : ℝ)*x 1 + (4240355523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87288079/200000000 : ℝ)^8337 ≤ (33317103091377/100000000000000 : ℝ)^6289 := by
    have hnat : (87288079 : ℕ)^8337*100000000000000^6289 ≤ 33317103091377^6289*200000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87288079 200000000 33317103091377 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280755113/625000000 : ℝ)^8337 ≤ (17307643886381/50000000000000 : ℝ)^6289 := by
    have hnat : (280755113 : ℕ)^8337*50000000000000^6289 ≤ 17307643886381^6289*625000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280755113 625000000 17307643886381 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4240355523/10000000000 : ℝ)^8337 ≤ (32067609122797/100000000000000 : ℝ)^6289 := by
    have hnat : (4240355523 : ℕ)^8337*100000000000000^6289 ≤ 32067609122797^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4240355523 10000000000 32067609122797 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(87288079/200000000 : ℝ), (280755113/625000000 : ℝ), (4240355523/10000000000 : ℝ)] ![(33317103091377/100000000000000 : ℝ), (17307643886381/50000000000000 : ℝ), (32067609122797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(87288079/200000000 : ℝ)|^8337 ≤ (33317103091377/100000000000000 : ℝ)^6289
        have hw : |(87288079/200000000 : ℝ)|=(87288079/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(280755113/625000000 : ℝ)|^8337 ≤ (17307643886381/50000000000000 : ℝ)^6289
        have hw : |(280755113/625000000 : ℝ)|=(280755113/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4240355523/10000000000 : ℝ)|^8337 ≤ (32067609122797/100000000000000 : ℝ)^6289
        have hw : |(4240355523/10000000000 : ℝ)|=(4240355523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1144_s10 (p A d : ℝ) (hA : A ≤ 3) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37378183/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (281/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11357/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11357/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14049/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (281/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11357/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (281/2000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11357/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (281/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11357/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (281/2000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11357/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (281/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11357/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (281/2000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11357/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11357/100000 : ℝ) ^ (521/128 : ℝ) ≤ (14276696487584349/100000000000000000000 : ℝ) := by
    have hpowers : (11357/100000 : ℝ)^521 ≤ (14276696487584349/100000000000000000000 : ℝ)^128 := by
      have hnat : (11357 : ℕ)^521*100000000000000000000^128 ≤ 14276696487584349^128*100000^521 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11357 100000 14276696487584349 100000000000000000000 521 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11357/100000 : ℝ)) (X := (14276696487584349/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hpowhi : (281/2000 : ℝ) ^ (521/128 : ℝ) ≤ (1060782411433317/3125000000000000000 : ℝ) := by
    have hpowers : (281/2000 : ℝ)^521 ≤ (1060782411433317/3125000000000000000 : ℝ)^128 := by
      have hnat : (281 : ℕ)^521*3125000000000000000^128 ≤ 1060782411433317^128*2000^521 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        281 2000 1060782411433317 3125000000000000000 521 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (281/2000 : ℝ)) (X := (1060782411433317/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014276696487584349/50000000000000000000 : ℝ) ≤ (5000350714085501/5000000000000000 : ℝ) ^ (521/128 : ℝ) := by
    have hpowers : (50014276696487584349/50000000000000000000 : ℝ)^128 ≤ (5000350714085501/5000000000000000 : ℝ)^521 := by
      have hnat : (50014276696487584349 : ℕ)^128*5000000000000000^521 ≤ 5000350714085501^521*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014276696487584349 50000000000000000000 5000350714085501 5000000000000000 128 521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000350714085501/5000000000000000 : ℝ)) (X := (50014276696487584349/50000000000000000000 : ℝ)) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048221733653450493/100000000000000000000 : ℝ) ≤ (10001184502809209/10000000000000000 : ℝ) ^ (521/128 : ℝ) := by
    have hpowers : (100048221733653450493/100000000000000000000 : ℝ)^128 ≤ (10001184502809209/10000000000000000 : ℝ)^521 := by
      have hnat : (100048221733653450493 : ℕ)^128*10000000000000000^521 ≤ 10001184502809209^521*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048221733653450493 100000000000000000000 10001184502809209 10000000000000000 128 521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001184502809209/10000000000000000 : ℝ)) (X := (100048221733653450493/100000000000000000000 : ℝ)) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563560782411433317/1562500000000000000 : ℝ) ≤ (1250208447180927/1250000000000000 : ℝ) ^ (521/128 : ℝ) := by
    have hpowers : (1563560782411433317/1562500000000000000 : ℝ)^128 ≤ (1250208447180927/1250000000000000 : ℝ)^521 := by
      have hnat : (1563560782411433317 : ℕ)^128*1250000000000000^521 ≤ 1250208447180927^521*1562500000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563560782411433317 1562500000000000000 1250208447180927 1250000000000000 128 521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250208447180927/1250000000000000 : ℝ)) (X := (1563560782411433317/1562500000000000000 : ℝ)) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14276696487584349/100000000000000000000 : ℝ) ≤ ((6730229097183068647/6732500000000000000 : ℝ)+2*(483074638207/269300000000000 : ℝ)*(11357/100000 : ℝ))^(521/128 : ℝ) := by
    rw [show (6730229097183068647/6732500000000000000 : ℝ)+2*(483074638207/269300000000000 : ℝ)*(11357/100000 : ℝ)=(5000350714085501/5000000000000000 : ℝ) by norm_num, show 1+2*(14276696487584349/100000000000000000000 : ℝ)=(50014276696487584349/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1060782411433317/3125000000000000000 : ℝ)+(14276696487584349/100000000000000000000 : ℝ) ≤ ((6730229097183068647/6732500000000000000 : ℝ)+(483074638207/269300000000000 : ℝ)*((281/2000 : ℝ)+(11357/100000 : ℝ)))^(521/128 : ℝ) := by
    rw [show (6730229097183068647/6732500000000000000 : ℝ)+(483074638207/269300000000000 : ℝ)*((281/2000 : ℝ)+(11357/100000 : ℝ))=(10001184502809209/10000000000000000 : ℝ) by norm_num, show 1+(1060782411433317/3125000000000000000 : ℝ)+(14276696487584349/100000000000000000000 : ℝ)=(100048221733653450493/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1060782411433317/3125000000000000000 : ℝ) ≤ ((6730229097183068647/6732500000000000000 : ℝ)+2*(483074638207/269300000000000 : ℝ)*(281/2000 : ℝ))^(521/128 : ℝ) := by
    rw [show (6730229097183068647/6732500000000000000 : ℝ)+2*(483074638207/269300000000000 : ℝ)*(281/2000 : ℝ)=(1250208447180927/1250000000000000 : ℝ) by norm_num, show 1+2*(1060782411433317/3125000000000000000 : ℝ)=(1563560782411433317/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6730229097183068647/6732500000000000000 : ℝ)*(X 1 0+X 2 0)+(483074638207/269300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (521/128 : ℝ)) (lo := (11357/100000 : ℝ)) (hi := (281/2000 : ℝ)) (c := (6730229097183068647/6732500000000000000 : ℝ)) (alpha := (483074638207/269300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6730229097183068647/6732500000000000000 : ℝ)*(X 0 1+X 2 1)+(483074638207/269300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (521/128 : ℝ)) (lo := (11357/100000 : ℝ)) (hi := (281/2000 : ℝ)) (c := (6730229097183068647/6732500000000000000 : ℝ)) (alpha := (483074638207/269300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6730229097183068647/6732500000000000000 : ℝ)*(X 0 2+X 1 2)+(483074638207/269300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (521/128 : ℝ)) (lo := (11357/100000 : ℝ)) (hi := (281/2000 : ℝ)) (c := (6730229097183068647/6732500000000000000 : ℝ)) (alpha := (483074638207/269300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2165931337/10000000000 : ℝ)*X 0 0+(2696472091/5000000000 : ℝ)*X 0 1+(2632912379/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s10_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344738699/10000000000 : ℝ)*X 1 0+(-557601567/2500000000 : ℝ)*X 1 1+(2632912451/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s10_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-108296803/500000000 : ℝ)*X 0 0+(2633072017/5000000000 : ℝ)*X 0 1+(5392623861/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s10_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1062505463/2000000000 : ℝ)*X 1 0+(-13147551/62500000 : ℝ)*X 1 1+(5392623489/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s10_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((5312526973/10000000000 : ℝ)*X 2 0+(337038993/625000000 : ℝ)*X 2 1+(-26295101/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s10_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((87288079/200000000 : ℝ)*X 0 0+(280755113/625000000 : ℝ)*X 0 1+(4240355523/10000000000 : ℝ)*X 0 2+(87288079/200000000 : ℝ)*X 1 0+(280755113/625000000 : ℝ)*X 1 1+(4240355523/10000000000 : ℝ)*X 1 2+(87288079/200000000 : ℝ)*X 2 0+(280755113/625000000 : ℝ)*X 2 1+(4240355523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_s10_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (300883589043382489103852541/168312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (97364921/10000000000000 : ℝ)*(base19) + (113734873/25000000000000 : ℝ)*(base23) + (15433469/10000000000000 : ℝ)*(lower1) + (9589469/100000000000000 : ℝ)*(lower4) + (8475811/5000000000000 : ℝ)*(upper5) + (2969738858959899/50000000000000 : ℝ)*(major0) + (2969738858959899/50000000000000 : ℝ)*(major1) + (2969738858959899/50000000000000 : ℝ)*(major2) + (2284895041/50000000000000 : ℝ)*(sp0) + (4581174881/100000000000000 : ℝ)*(sp1) + (1976598582546871/25000000000000 : ℝ)*(sp2) + (316255733806139/4000000000000 : ℝ)*(sp3) + (3953199222519037/50000000000000 : ℝ)*(sp4) + (1986278238136869/50000000000000 : ℝ)*(sp5) + (1986278238136869/50000000000000 : ℝ)*(f.failure) + (3953199449988783/50000000000000 : ℝ)*(f.sum) + (2420954719131/841562500000000000000000000 : ℝ)*base65 + (2340617856438011653/336625000000000000000000000000000 : ℝ)*base67 + (1343322812086761653/336625000000000000000000000000000 : ℝ)*base69 + (1114609826309488347/336625000000000000000000000000000 : ℝ)*base72 + (65738029281523/6732500000000000000000000000 : ℝ)*base73 + (4406187828524136653/336625000000000000000000000000000 : ℝ)*base75 + (4283212255853761653/336625000000000000000000000000000 : ℝ)*base77 + (1789985772071488347/336625000000000000000000000000000 : ℝ)*base80 + (3363601597519/3366250000000000000000000000 : ℝ)*base81 + (6470973/1250000000000000000000 : ℝ)*base90 + (6470973/1250000000000000000000 : ℝ)*base92 + (6470973/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1144_s10 (p A d : ℝ) (hA : A ≤ 3) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37378183/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (281/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11357/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11357/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1144_s10 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1144_box_0 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2039115361/10000000000 : ℝ)*x 0 + (1344069389/2500000000 : ℝ)*x 1 + (1075255603/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2039115361/10000000000 : ℝ)^8337 ≤ (12149626528271/100000000000000 : ℝ)^6289 := by
    have hnat : (2039115361 : ℕ)^8337*100000000000000^6289 ≤ 12149626528271^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039115361 10000000000 12149626528271 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1344069389/2500000000 : ℝ)^8337 ≤ (4392518424431/10000000000000 : ℝ)^6289 := by
    have hnat : (1344069389 : ℕ)^8337*10000000000000^6289 ≤ 4392518424431^6289*2500000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344069389 2500000000 4392518424431 10000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1075255603/2000000000 : ℝ)^8337 ≤ (43925189215643/100000000000000 : ℝ)^6289 := by
    have hnat : (1075255603 : ℕ)^8337*100000000000000^6289 ≤ 43925189215643^6289*2000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075255603 2000000000 43925189215643 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2039115361/10000000000 : ℝ), (1344069389/2500000000 : ℝ), (1075255603/2000000000 : ℝ)] ![(12149626528271/100000000000000 : ℝ), (4392518424431/10000000000000 : ℝ), (43925189215643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2039115361/10000000000 : ℝ)|^8337 ≤ (12149626528271/100000000000000 : ℝ)^6289
        have hw : |(-2039115361/10000000000 : ℝ)|=(2039115361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1344069389/2500000000 : ℝ)|^8337 ≤ (4392518424431/10000000000000 : ℝ)^6289
        have hw : |(1344069389/2500000000 : ℝ)|=(1344069389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1075255603/2000000000 : ℝ)|^8337 ≤ (43925189215643/100000000000000 : ℝ)^6289
        have hw : |(1075255603/2000000000 : ℝ)|=(1075255603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_box_1 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (662000611/1250000000 : ℝ)*x 0 + (-2147983519/10000000000 : ℝ)*x 1 + (2688139173/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (662000611/1250000000 : ℝ)^8337 ≤ (43057888655287/100000000000000 : ℝ)^6289 := by
    have hnat : (662000611 : ℕ)^8337*100000000000000^6289 ≤ 43057888655287^6289*1250000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      662000611 1250000000 43057888655287 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2147983519/10000000000 : ℝ)^8337 ≤ (1627114816591/12500000000000 : ℝ)^6289 := by
    have hnat : (2147983519 : ℕ)^8337*12500000000000^6289 ≤ 1627114816591^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147983519 10000000000 1627114816591 12500000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2688139173/5000000000 : ℝ)^8337 ≤ (21962596400317/50000000000000 : ℝ)^6289 := by
    have hnat : (2688139173 : ℕ)^8337*50000000000000^6289 ≤ 21962596400317^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688139173 5000000000 21962596400317 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(662000611/1250000000 : ℝ), (-2147983519/10000000000 : ℝ), (2688139173/5000000000 : ℝ)] ![(43057888655287/100000000000000 : ℝ), (1627114816591/12500000000000 : ℝ), (21962596400317/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(662000611/1250000000 : ℝ)|^8337 ≤ (43057888655287/100000000000000 : ℝ)^6289
        have hw : |(662000611/1250000000 : ℝ)|=(662000611/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2147983519/10000000000 : ℝ)|^8337 ≤ (1627114816591/12500000000000 : ℝ)^6289
        have hw : |(-2147983519/10000000000 : ℝ)|=(2147983519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2688139173/5000000000 : ℝ)|^8337 ≤ (21962596400317/50000000000000 : ℝ)^6289
        have hw : |(2688139173/5000000000 : ℝ)|=(2688139173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_box_2 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296005851/10000000000 : ℝ)*x 0 + (5376277939/10000000000 : ℝ)*x 1 + (-268497847/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296005851/10000000000 : ℝ)^8337 ≤ (43057899034367/100000000000000 : ℝ)^6289 := by
    have hnat : (5296005851 : ℕ)^8337*100000000000000^6289 ≤ 43057899034367^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296005851 10000000000 43057899034367 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5376277939/10000000000 : ℝ)^8337 ≤ (43925188392503/100000000000000 : ℝ)^6289 := by
    have hnat : (5376277939 : ℕ)^8337*100000000000000^6289 ≤ 43925188392503^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376277939 10000000000 43925188392503 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (268497847/1250000000 : ℝ)^8337 ≤ (13016912563829/100000000000000 : ℝ)^6289 := by
    have hnat : (268497847 : ℕ)^8337*100000000000000^6289 ≤ 13016912563829^6289*1250000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268497847 1250000000 13016912563829 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296005851/10000000000 : ℝ), (5376277939/10000000000 : ℝ), (-268497847/1250000000 : ℝ)] ![(43057899034367/100000000000000 : ℝ), (43925188392503/100000000000000 : ℝ), (13016912563829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296005851/10000000000 : ℝ)|^8337 ≤ (43057899034367/100000000000000 : ℝ)^6289
        have hw : |(5296005851/10000000000 : ℝ)|=(5296005851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5376277939/10000000000 : ℝ)|^8337 ≤ (43925188392503/100000000000000 : ℝ)^6289
        have hw : |(5376277939/10000000000 : ℝ)|=(5376277939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-268497847/1250000000 : ℝ)|^8337 ≤ (13016912563829/100000000000000 : ℝ)^6289
        have hw : |(-268497847/1250000000 : ℝ)|=(268497847/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_box_3 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4471910007/10000000000 : ℝ)*x 0 + (4312742589/10000000000 : ℝ)*x 1 + (431274221/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4471910007/10000000000 : ℝ)^8337 ≤ (17204689418723/50000000000000 : ℝ)^6289 := by
    have hnat : (4471910007 : ℕ)^8337*50000000000000^6289 ≤ 17204689418723^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4471910007 10000000000 17204689418723 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4312742589/10000000000 : ℝ)^8337 ≤ (32795312483763/100000000000000 : ℝ)^6289 := by
    have hnat : (4312742589 : ℕ)^8337*100000000000000^6289 ≤ 32795312483763^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312742589 10000000000 32795312483763 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (431274221/1000000000 : ℝ)^8337 ≤ (6559061732643/20000000000000 : ℝ)^6289 := by
    have hnat : (431274221 : ℕ)^8337*20000000000000^6289 ≤ 6559061732643^6289*1000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      431274221 1000000000 6559061732643 20000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4471910007/10000000000 : ℝ), (4312742589/10000000000 : ℝ), (431274221/1000000000 : ℝ)] ![(17204689418723/50000000000000 : ℝ), (32795312483763/100000000000000 : ℝ), (6559061732643/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4471910007/10000000000 : ℝ)|^8337 ≤ (17204689418723/50000000000000 : ℝ)^6289
        have hw : |(4471910007/10000000000 : ℝ)|=(4471910007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4312742589/10000000000 : ℝ)|^8337 ≤ (32795312483763/100000000000000 : ℝ)^6289
        have hw : |(4312742589/10000000000 : ℝ)|=(4312742589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(431274221/1000000000 : ℝ)|^8337 ≤ (6559061732643/20000000000000 : ℝ)^6289
        have hw : |(431274221/1000000000 : ℝ)|=(431274221/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_box_4 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1147068529/5000000000 : ℝ)*x 0 + (528116959/1000000000 : ℝ)*x 1 + (5281169867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1147068529/5000000000 : ℝ)^8337 ≤ (568154371647/4000000000000 : ℝ)^6289 := by
    have hnat : (1147068529 : ℕ)^8337*4000000000000^6289 ≤ 568154371647^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1147068529 5000000000 568154371647 4000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528116959/1000000000 : ℝ)^8337 ≤ (10724517214109/25000000000000 : ℝ)^6289 := by
    have hnat : (528116959 : ℕ)^8337*25000000000000^6289 ≤ 10724517214109^6289*1000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528116959 1000000000 10724517214109 25000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5281169867/10000000000 : ℝ)^8337 ≤ (21449035919589/50000000000000 : ℝ)^6289 := by
    have hnat : (5281169867 : ℕ)^8337*50000000000000^6289 ≤ 21449035919589^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281169867 10000000000 21449035919589 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1147068529/5000000000 : ℝ), (528116959/1000000000 : ℝ), (5281169867/10000000000 : ℝ)] ![(568154371647/4000000000000 : ℝ), (10724517214109/25000000000000 : ℝ), (21449035919589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1147068529/5000000000 : ℝ)|^8337 ≤ (568154371647/4000000000000 : ℝ)^6289
        have hw : |(-1147068529/5000000000 : ℝ)|=(1147068529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(528116959/1000000000 : ℝ)|^8337 ≤ (10724517214109/25000000000000 : ℝ)^6289
        have hw : |(528116959/1000000000 : ℝ)|=(528116959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5281169867/10000000000 : ℝ)|^8337 ≤ (21449035919589/50000000000000 : ℝ)^6289
        have hw : |(5281169867/10000000000 : ℝ)|=(5281169867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_box_5 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5363196661/10000000000 : ℝ)*x 0 + (-2185401897/10000000000 : ℝ)*x 1 + (660146179/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5363196661/10000000000 : ℝ)^8337 ≤ (43783563981221/100000000000000 : ℝ)^6289 := by
    have hnat : (5363196661 : ℕ)^8337*100000000000000^6289 ≤ 43783563981221^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363196661 10000000000 43783563981221 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2185401897/10000000000 : ℝ)^8337 ≤ (13318368842461/100000000000000 : ℝ)^6289 := by
    have hnat : (2185401897 : ℕ)^8337*100000000000000^6289 ≤ 13318368842461^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185401897 10000000000 13318368842461 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (660146179/1250000000 : ℝ)^8337 ≤ (42898067155089/100000000000000 : ℝ)^6289 := by
    have hnat : (660146179 : ℕ)^8337*100000000000000^6289 ≤ 42898067155089^6289*1250000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660146179 1250000000 42898067155089 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5363196661/10000000000 : ℝ), (-2185401897/10000000000 : ℝ), (660146179/1250000000 : ℝ)] ![(43783563981221/100000000000000 : ℝ), (13318368842461/100000000000000 : ℝ), (42898067155089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5363196661/10000000000 : ℝ)|^8337 ≤ (43783563981221/100000000000000 : ℝ)^6289
        have hw : |(5363196661/10000000000 : ℝ)|=(5363196661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2185401897/10000000000 : ℝ)|^8337 ≤ (13318368842461/100000000000000 : ℝ)^6289
        have hw : |(-2185401897/10000000000 : ℝ)|=(2185401897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(660146179/1250000000 : ℝ)|^8337 ≤ (42898067155089/100000000000000 : ℝ)^6289
        have hw : |(660146179/1250000000 : ℝ)|=(660146179/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_box_6 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1340799077/2500000000 : ℝ)*x 0 + (5281169363/10000000000 : ℝ)*x 1 + (-1092701231/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340799077/2500000000 : ℝ)^8337 ≤ (5472945020123/12500000000000 : ℝ)^6289 := by
    have hnat : (1340799077 : ℕ)^8337*12500000000000^6289 ≤ 5472945020123^6289*2500000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340799077 2500000000 5472945020123 12500000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5281169363/10000000000 : ℝ)^8337 ≤ (670282287689/1562500000000 : ℝ)^6289 := by
    have hnat : (5281169363 : ℕ)^8337*1562500000000^6289 ≤ 670282287689^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5281169363 10000000000 670282287689 1562500000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1092701231/5000000000 : ℝ)^8337 ≤ (2663674681399/20000000000000 : ℝ)^6289 := by
    have hnat : (1092701231 : ℕ)^8337*20000000000000^6289 ≤ 2663674681399^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092701231 5000000000 2663674681399 20000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340799077/2500000000 : ℝ), (5281169363/10000000000 : ℝ), (-1092701231/5000000000 : ℝ)] ![(5472945020123/12500000000000 : ℝ), (670282287689/1562500000000 : ℝ), (2663674681399/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340799077/2500000000 : ℝ)|^8337 ≤ (5472945020123/12500000000000 : ℝ)^6289
        have hw : |(1340799077/2500000000 : ℝ)|=(1340799077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5281169363/10000000000 : ℝ)|^8337 ≤ (670282287689/1562500000000 : ℝ)^6289
        have hw : |(5281169363/10000000000 : ℝ)|=(5281169363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1092701231/5000000000 : ℝ)|^8337 ≤ (2663674681399/20000000000000 : ℝ)^6289
        have hw : |(-1092701231/5000000000 : ℝ)|=(1092701231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_box_7 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4256515881/10000000000 : ℝ)*x 0 + (2210209373/5000000000 : ℝ)*x 1 + (2210209269/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4256515881/10000000000 : ℝ)^8337 ≤ (32229720194329/100000000000000 : ℝ)^6289 := by
    have hnat : (4256515881 : ℕ)^8337*100000000000000^6289 ≤ 32229720194329^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4256515881 10000000000 32229720194329 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2210209373/5000000000 : ℝ)^8337 ≤ (33885140951553/100000000000000 : ℝ)^6289 := by
    have hnat : (2210209373 : ℕ)^8337*100000000000000^6289 ≤ 33885140951553^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210209373 5000000000 33885140951553 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2210209269/5000000000 : ℝ)^8337 ≤ (16942569418941/50000000000000 : ℝ)^6289 := by
    have hnat : (2210209269 : ℕ)^8337*50000000000000^6289 ≤ 16942569418941^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210209269 5000000000 16942569418941 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4256515881/10000000000 : ℝ), (2210209373/5000000000 : ℝ), (2210209269/5000000000 : ℝ)] ![(32229720194329/100000000000000 : ℝ), (33885140951553/100000000000000 : ℝ), (16942569418941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4256515881/10000000000 : ℝ)|^8337 ≤ (32229720194329/100000000000000 : ℝ)^6289
        have hw : |(4256515881/10000000000 : ℝ)|=(4256515881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2210209373/5000000000 : ℝ)|^8337 ≤ (33885140951553/100000000000000 : ℝ)^6289
        have hw : |(2210209373/5000000000 : ℝ)|=(2210209373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2210209269/5000000000 : ℝ)|^8337 ≤ (16942569418941/50000000000000 : ℝ)^6289
        have hw : |(2210209269/5000000000 : ℝ)|=(2210209269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_box_8 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-224080597/1000000000 : ℝ)*x 0 + (2608241391/5000000000 : ℝ)*x 1 + (269294299/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (224080597/1000000000 : ℝ)^8337 ≤ (13767805598049/100000000000000 : ℝ)^6289 := by
    have hnat : (224080597 : ℕ)^8337*100000000000000^6289 ≤ 13767805598049^6289*1000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224080597 1000000000 13767805598049 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608241391/5000000000 : ℝ)^8337 ≤ (42202913058983/100000000000000 : ℝ)^6289 := by
    have hnat : (2608241391 : ℕ)^8337*100000000000000^6289 ≤ 42202913058983^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608241391 5000000000 42202913058983 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269294299/500000000 : ℝ)^8337 ≤ (44029281333509/100000000000000 : ℝ)^6289 := by
    have hnat : (269294299 : ℕ)^8337*100000000000000^6289 ≤ 44029281333509^6289*500000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269294299 500000000 44029281333509 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-224080597/1000000000 : ℝ), (2608241391/5000000000 : ℝ), (269294299/500000000 : ℝ)] ![(13767805598049/100000000000000 : ℝ), (42202913058983/100000000000000 : ℝ), (44029281333509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-224080597/1000000000 : ℝ)|^8337 ≤ (13767805598049/100000000000000 : ℝ)^6289
        have hw : |(-224080597/1000000000 : ℝ)|=(224080597/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608241391/5000000000 : ℝ)|^8337 ≤ (42202913058983/100000000000000 : ℝ)^6289
        have hw : |(2608241391/5000000000 : ℝ)|=(2608241391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269294299/500000000 : ℝ)|^8337 ≤ (44029281333509/100000000000000 : ℝ)^6289
        have hw : |(269294299/500000000 : ℝ)|=(269294299/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_box_9 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (528921433/1000000000 : ℝ)*x 0 + (-428826793/2000000000 : ℝ)*x 1 + (1077177201/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528921433/1000000000 : ℝ)^8337 ≤ (10746179063053/25000000000000 : ℝ)^6289 := by
    have hnat : (528921433 : ℕ)^8337*25000000000000^6289 ≤ 10746179063053^6289*1000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528921433 1000000000 10746179063053 25000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (428826793/2000000000 : ℝ)^8337 ≤ (405812566321/3125000000000 : ℝ)^6289 := by
    have hnat : (428826793 : ℕ)^8337*3125000000000^6289 ≤ 405812566321^6289*2000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428826793 2000000000 405812566321 3125000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077177201/2000000000 : ℝ)^8337 ≤ (11007320401109/25000000000000 : ℝ)^6289 := by
    have hnat : (1077177201 : ℕ)^8337*25000000000000^6289 ≤ 11007320401109^6289*2000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077177201 2000000000 11007320401109 25000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528921433/1000000000 : ℝ), (-428826793/2000000000 : ℝ), (1077177201/2000000000 : ℝ)] ![(10746179063053/25000000000000 : ℝ), (405812566321/3125000000000 : ℝ), (11007320401109/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528921433/1000000000 : ℝ)|^8337 ≤ (10746179063053/25000000000000 : ℝ)^6289
        have hw : |(528921433/1000000000 : ℝ)|=(528921433/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-428826793/2000000000 : ℝ)|^8337 ≤ (405812566321/3125000000000 : ℝ)^6289
        have hw : |(-428826793/2000000000 : ℝ)|=(428826793/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077177201/2000000000 : ℝ)|^8337 ≤ (11007320401109/25000000000000 : ℝ)^6289
        have hw : |(1077177201/2000000000 : ℝ)|=(1077177201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_box_10 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2644607051/5000000000 : ℝ)*x 0 + (1346471479/2500000000 : ℝ)*x 1 + (-268016799/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644607051/5000000000 : ℝ)^8337 ≤ (21492356897943/50000000000000 : ℝ)^6289 := by
    have hnat : (2644607051 : ℕ)^8337*50000000000000^6289 ≤ 21492356897943^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644607051 5000000000 21492356897943 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346471479/2500000000 : ℝ)^8337 ≤ (687957509999/1562500000000 : ℝ)^6289 := by
    have hnat : (1346471479 : ℕ)^8337*1562500000000^6289 ≤ 687957509999^6289*2500000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346471479 2500000000 687957509999 1562500000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (268016799/1250000000 : ℝ)^8337 ≤ (6493002775289/50000000000000 : ℝ)^6289 := by
    have hnat : (268016799 : ℕ)^8337*50000000000000^6289 ≤ 6493002775289^6289*1250000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268016799 1250000000 6493002775289 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644607051/5000000000 : ℝ), (1346471479/2500000000 : ℝ), (-268016799/1250000000 : ℝ)] ![(21492356897943/50000000000000 : ℝ), (687957509999/1562500000000 : ℝ), (6493002775289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644607051/5000000000 : ℝ)|^8337 ≤ (21492356897943/50000000000000 : ℝ)^6289
        have hw : |(2644607051/5000000000 : ℝ)|=(2644607051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346471479/2500000000 : ℝ)|^8337 ≤ (687957509999/1562500000000 : ℝ)^6289
        have hw : |(1346471479/2500000000 : ℝ)|=(1346471479/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-268016799/1250000000 : ℝ)|^8337 ≤ (6493002775289/50000000000000 : ℝ)^6289
        have hw : |(-268016799/1250000000 : ℝ)|=(268016799/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_box_11 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4493396657/10000000000 : ℝ)*x 0 + (1075464633/2500000000 : ℝ)*x 1 + (4301858589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4493396657/10000000000 : ℝ)^8337 ≤ (6925743981707/20000000000000 : ℝ)^6289 := by
    have hnat : (4493396657 : ℕ)^8337*20000000000000^6289 ≤ 6925743981707^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493396657 10000000000 6925743981707 20000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1075464633/2500000000 : ℝ)^8337 ≤ (32685639754207/100000000000000 : ℝ)^6289 := by
    have hnat : (1075464633 : ℕ)^8337*100000000000000^6289 ≤ 32685639754207^6289*2500000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075464633 2500000000 32685639754207 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4301858589/10000000000 : ℝ)^8337 ≤ (32685640328329/100000000000000 : ℝ)^6289 := by
    have hnat : (4301858589 : ℕ)^8337*100000000000000^6289 ≤ 32685640328329^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301858589 10000000000 32685640328329 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4493396657/10000000000 : ℝ), (1075464633/2500000000 : ℝ), (4301858589/10000000000 : ℝ)] ![(6925743981707/20000000000000 : ℝ), (32685639754207/100000000000000 : ℝ), (32685640328329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4493396657/10000000000 : ℝ)|^8337 ≤ (6925743981707/20000000000000 : ℝ)^6289
        have hw : |(4493396657/10000000000 : ℝ)|=(4493396657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1075464633/2500000000 : ℝ)|^8337 ≤ (32685639754207/100000000000000 : ℝ)^6289
        have hw : |(1075464633/2500000000 : ℝ)|=(1075464633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4301858589/10000000000 : ℝ)|^8337 ≤ (32685640328329/100000000000000 : ℝ)^6289
        have hw : |(4301858589/10000000000 : ℝ)|=(4301858589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_box_12 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2092764147/10000000000 : ℝ)*x 0 + (67996107/125000000 : ℝ)*x 1 + (1054626157/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2092764147/10000000000 : ℝ)^8337 ≤ (12575180735791/100000000000000 : ℝ)^6289 := by
    have hnat : (2092764147 : ℕ)^8337*100000000000000^6289 ≤ 12575180735791^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2092764147 10000000000 12575180735791 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (67996107/125000000 : ℝ)^8337 ≤ (5576661368359/12500000000000 : ℝ)^6289 := by
    have hnat : (67996107 : ℕ)^8337*12500000000000^6289 ≤ 5576661368359^6289*125000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67996107 125000000 5576661368359 12500000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054626157/2000000000 : ℝ)^8337 ≤ (42811528308421/100000000000000 : ℝ)^6289 := by
    have hnat : (1054626157 : ℕ)^8337*100000000000000^6289 ≤ 42811528308421^6289*2000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054626157 2000000000 42811528308421 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2092764147/10000000000 : ℝ), (67996107/125000000 : ℝ), (1054626157/2000000000 : ℝ)] ![(12575180735791/100000000000000 : ℝ), (5576661368359/12500000000000 : ℝ), (42811528308421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2092764147/10000000000 : ℝ)|^8337 ≤ (12575180735791/100000000000000 : ℝ)^6289
        have hw : |(-2092764147/10000000000 : ℝ)|=(2092764147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(67996107/125000000 : ℝ)|^8337 ≤ (5576661368359/12500000000000 : ℝ)^6289
        have hw : |(67996107/125000000 : ℝ)|=(67996107/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1054626157/2000000000 : ℝ)|^8337 ≤ (42811528308421/100000000000000 : ℝ)^6289
        have hw : |(1054626157/2000000000 : ℝ)|=(1054626157/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_box_13 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (671109109/1250000000 : ℝ)*x 0 + (-1094253683/5000000000 : ℝ)*x 1 + (1318282809/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671109109/1250000000 : ℝ)^8337 ≤ (5480625457601/12500000000000 : ℝ)^6289 := by
    have hnat : (671109109 : ℕ)^8337*12500000000000^6289 ≤ 5480625457601^6289*1250000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671109109 1250000000 5480625457601 12500000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1094253683/5000000000 : ℝ)^8337 ≤ (6671731585173/50000000000000 : ℝ)^6289 := by
    have hnat : (1094253683 : ℕ)^8337*50000000000000^6289 ≤ 6671731585173^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094253683 5000000000 6671731585173 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318282809/2500000000 : ℝ)^8337 ≤ (42811533162389/100000000000000 : ℝ)^6289 := by
    have hnat : (1318282809 : ℕ)^8337*100000000000000^6289 ≤ 42811533162389^6289*2500000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318282809 2500000000 42811533162389 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671109109/1250000000 : ℝ), (-1094253683/5000000000 : ℝ), (1318282809/2500000000 : ℝ)] ![(5480625457601/12500000000000 : ℝ), (6671731585173/50000000000000 : ℝ), (42811533162389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671109109/1250000000 : ℝ)|^8337 ≤ (5480625457601/12500000000000 : ℝ)^6289
        have hw : |(671109109/1250000000 : ℝ)|=(671109109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1094253683/5000000000 : ℝ)|^8337 ≤ (6671731585173/50000000000000 : ℝ)^6289
        have hw : |(-1094253683/5000000000 : ℝ)|=(1094253683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318282809/2500000000 : ℝ)|^8337 ≤ (42811533162389/100000000000000 : ℝ)^6289
        have hw : |(1318282809/2500000000 : ℝ)|=(1318282809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_box_14 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684436531/5000000000 : ℝ)*x 0 + (5273131197/10000000000 : ℝ)*x 1 + (-1094253581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684436531/5000000000 : ℝ)^8337 ≤ (21922502858867/50000000000000 : ℝ)^6289 := by
    have hnat : (2684436531 : ℕ)^8337*50000000000000^6289 ≤ 21922502858867^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684436531 5000000000 21922502858867 50000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5273131197/10000000000 : ℝ)^8337 ≤ (8562306548529/20000000000000 : ℝ)^6289 := by
    have hnat : (5273131197 : ℕ)^8337*20000000000000^6289 ≤ 8562306548529^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5273131197 10000000000 8562306548529 20000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1094253581/5000000000 : ℝ)^8337 ≤ (2668692304301/20000000000000 : ℝ)^6289 := by
    have hnat : (1094253581 : ℕ)^8337*20000000000000^6289 ≤ 2668692304301^6289*5000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094253581 5000000000 2668692304301 20000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684436531/5000000000 : ℝ), (5273131197/10000000000 : ℝ), (-1094253581/5000000000 : ℝ)] ![(21922502858867/50000000000000 : ℝ), (8562306548529/20000000000000 : ℝ), (2668692304301/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684436531/5000000000 : ℝ)|^8337 ≤ (21922502858867/50000000000000 : ℝ)^6289
        have hw : |(2684436531/5000000000 : ℝ)|=(2684436531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5273131197/10000000000 : ℝ)|^8337 ≤ (8562306548529/20000000000000 : ℝ)^6289
        have hw : |(5273131197/10000000000 : ℝ)|=(5273131197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1094253581/5000000000 : ℝ)|^8337 ≤ (2668692304301/20000000000000 : ℝ)^6289
        have hw : |(-1094253581/5000000000 : ℝ)|=(1094253581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1144_box_15 (p : ℝ) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4238078471/10000000000 : ℝ)*x 0 + (276844703/625000000 : ℝ)*x 1 + (442951503/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4238078471/10000000000 : ℝ)^8337 ≤ (32044783245051/100000000000000 : ℝ)^6289 := by
    have hnat : (4238078471 : ℕ)^8337*100000000000000^6289 ≤ 32044783245051^6289*10000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238078471 10000000000 32044783245051 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (276844703/625000000 : ℝ)^8337 ≤ (8494402369453/25000000000000 : ℝ)^6289 := by
    have hnat : (276844703 : ℕ)^8337*25000000000000^6289 ≤ 8494402369453^6289*625000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276844703 625000000 8494402369453 25000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (442951503/1000000000 : ℝ)^8337 ≤ (33977607261039/100000000000000 : ℝ)^6289 := by
    have hnat : (442951503 : ℕ)^8337*100000000000000^6289 ≤ 33977607261039^6289*1000000000^8337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442951503 1000000000 33977607261039 100000000000000 8337 6289 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8337/2048 : ℝ)) 8337 6289 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4238078471/10000000000 : ℝ), (276844703/625000000 : ℝ), (442951503/1000000000 : ℝ)] ![(32044783245051/100000000000000 : ℝ), (8494402369453/25000000000000 : ℝ), (33977607261039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4238078471/10000000000 : ℝ)|^8337 ≤ (32044783245051/100000000000000 : ℝ)^6289
        have hw : |(4238078471/10000000000 : ℝ)|=(4238078471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(276844703/625000000 : ℝ)|^8337 ≤ (8494402369453/25000000000000 : ℝ)^6289
        have hw : |(276844703/625000000 : ℝ)|=(276844703/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(442951503/1000000000 : ℝ)|^8337 ≤ (33977607261039/100000000000000 : ℝ)^6289
        have hw : |(442951503/1000000000 : ℝ)|=(442951503/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1144_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37378183/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11357/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62231/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(593/1000 : ℝ) ∧ (39907/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83129/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14049/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11357/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14049/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11357/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14049/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11357/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14049/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11357/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14049/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11357/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14049/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11357/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11357/100000 : ℝ) ^ (521/128 : ℝ) ≤ (14276696487584349/100000000000000000000 : ℝ) := by
    have hpowers : (11357/100000 : ℝ)^521 ≤ (14276696487584349/100000000000000000000 : ℝ)^128 := by
      have hnat : (11357 : ℕ)^521*100000000000000000000^128 ≤ 14276696487584349^128*100000^521 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11357 100000 14276696487584349 100000000000000000000 521 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11357/100000 : ℝ)) (X := (14276696487584349/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hpowhi : (14049/100000 : ℝ) ^ (521/128 : ℝ) ≤ (33935204296599913/100000000000000000000 : ℝ) := by
    have hpowers : (14049/100000 : ℝ)^521 ≤ (33935204296599913/100000000000000000000 : ℝ)^128 := by
      have hnat : (14049 : ℕ)^521*100000000000000000000^128 ≤ 33935204296599913^128*100000^521 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14049 100000 33935204296599913 100000000000000000000 521 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14049/100000 : ℝ)) (X := (33935204296599913/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014276696487584349/50000000000000000000 : ℝ) ≤ (5000350714085501/5000000000000000 : ℝ) ^ (521/128 : ℝ) := by
    have hpowers : (50014276696487584349/50000000000000000000 : ℝ)^128 ≤ (5000350714085501/5000000000000000 : ℝ)^521 := by
      have hnat : (50014276696487584349 : ℕ)^128*5000000000000000^521 ≤ 5000350714085501^521*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014276696487584349 50000000000000000000 5000350714085501 5000000000000000 128 521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000350714085501/5000000000000000 : ℝ)) (X := (50014276696487584349/50000000000000000000 : ℝ)) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024105950392092131/50000000000000000000 : ℝ) ≤ (625074016332609/625000000000000 : ℝ) ^ (521/128 : ℝ) := by
    have hpowers : (50024105950392092131/50000000000000000000 : ℝ)^128 ≤ (625074016332609/625000000000000 : ℝ)^521 := by
      have hnat : (50024105950392092131 : ℕ)^128*625000000000000^521 ≤ 625074016332609^521*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024105950392092131 50000000000000000000 625074016332609 625000000000000 128 521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625074016332609/625000000000000 : ℝ)) (X := (50024105950392092131/50000000000000000000 : ℝ)) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033935204296599913/50000000000000000000 : ℝ) ≤ (5000833547236243/5000000000000000 : ℝ) ^ (521/128 : ℝ) := by
    have hpowers : (50033935204296599913/50000000000000000000 : ℝ)^128 ≤ (5000833547236243/5000000000000000 : ℝ)^521 := by
      have hnat : (50033935204296599913 : ℕ)^128*5000000000000000^521 ≤ 5000833547236243^521*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033935204296599913 50000000000000000000 5000833547236243 5000000000000000 128 521 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000833547236243/5000000000000000 : ℝ)) (X := (50033935204296599913/50000000000000000000 : ℝ)) (by norm_num) 521 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14276696487584349/100000000000000000000 : ℝ) ≤ ((6727730293112595899/6730000000000000000 : ℝ)+2*(241416575371/134600000000000 : ℝ)*(11357/100000 : ℝ))^(521/128 : ℝ) := by
    rw [show (6727730293112595899/6730000000000000000 : ℝ)+2*(241416575371/134600000000000 : ℝ)*(11357/100000 : ℝ)=(5000350714085501/5000000000000000 : ℝ) by norm_num, show 1+2*(14276696487584349/100000000000000000000 : ℝ)=(50014276696487584349/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33935204296599913/100000000000000000000 : ℝ)+(14276696487584349/100000000000000000000 : ℝ) ≤ ((6727730293112595899/6730000000000000000 : ℝ)+(241416575371/134600000000000 : ℝ)*((14049/100000 : ℝ)+(11357/100000 : ℝ)))^(521/128 : ℝ) := by
    rw [show (6727730293112595899/6730000000000000000 : ℝ)+(241416575371/134600000000000 : ℝ)*((14049/100000 : ℝ)+(11357/100000 : ℝ))=(625074016332609/625000000000000 : ℝ) by norm_num, show 1+(33935204296599913/100000000000000000000 : ℝ)+(14276696487584349/100000000000000000000 : ℝ)=(50024105950392092131/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33935204296599913/100000000000000000000 : ℝ) ≤ ((6727730293112595899/6730000000000000000 : ℝ)+2*(241416575371/134600000000000 : ℝ)*(14049/100000 : ℝ))^(521/128 : ℝ) := by
    rw [show (6727730293112595899/6730000000000000000 : ℝ)+2*(241416575371/134600000000000 : ℝ)*(14049/100000 : ℝ)=(5000833547236243/5000000000000000 : ℝ) by norm_num, show 1+2*(33935204296599913/100000000000000000000 : ℝ)=(50033935204296599913/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6727730293112595899/6730000000000000000 : ℝ)*(X 1 0+X 2 0)+(241416575371/134600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (521/128 : ℝ)) (lo := (11357/100000 : ℝ)) (hi := (14049/100000 : ℝ)) (c := (6727730293112595899/6730000000000000000 : ℝ)) (alpha := (241416575371/134600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6727730293112595899/6730000000000000000 : ℝ)*(X 0 1+X 2 1)+(241416575371/134600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (521/128 : ℝ)) (lo := (11357/100000 : ℝ)) (hi := (14049/100000 : ℝ)) (c := (6727730293112595899/6730000000000000000 : ℝ)) (alpha := (241416575371/134600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6727730293112595899/6730000000000000000 : ℝ)*(X 0 2+X 1 2)+(241416575371/134600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (521/128 : ℝ)) (lo := (11357/100000 : ℝ)) (hi := (14049/100000 : ℝ)) (c := (6727730293112595899/6730000000000000000 : ℝ)) (alpha := (241416575371/134600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2039115361/10000000000 : ℝ)*X 0 0+(1344069389/2500000000 : ℝ)*X 0 1+(1075255603/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((662000611/1250000000 : ℝ)*X 1 0+(-2147983519/10000000000 : ℝ)*X 1 1+(2688139173/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5296005851/10000000000 : ℝ)*X 2 0+(5376277939/10000000000 : ℝ)*X 2 1+(-268497847/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4471910007/10000000000 : ℝ)*X 0 0+(4312742589/10000000000 : ℝ)*X 0 1+(431274221/1000000000 : ℝ)*X 0 2+(4471910007/10000000000 : ℝ)*X 1 0+(4312742589/10000000000 : ℝ)*X 1 1+(431274221/1000000000 : ℝ)*X 1 2+(4471910007/10000000000 : ℝ)*X 2 0+(4312742589/10000000000 : ℝ)*X 2 1+(431274221/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1147068529/5000000000 : ℝ)*X 0 0+(528116959/1000000000 : ℝ)*X 0 1+(5281169867/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5363196661/10000000000 : ℝ)*X 1 0+(-2185401897/10000000000 : ℝ)*X 1 1+(660146179/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1340799077/2500000000 : ℝ)*X 2 0+(5281169363/10000000000 : ℝ)*X 2 1+(-1092701231/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4256515881/10000000000 : ℝ)*X 0 0+(2210209373/5000000000 : ℝ)*X 0 1+(2210209269/5000000000 : ℝ)*X 0 2+(4256515881/10000000000 : ℝ)*X 1 0+(2210209373/5000000000 : ℝ)*X 1 1+(2210209269/5000000000 : ℝ)*X 1 2+(4256515881/10000000000 : ℝ)*X 2 0+(2210209373/5000000000 : ℝ)*X 2 1+(2210209269/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-224080597/1000000000 : ℝ)*X 0 0+(2608241391/5000000000 : ℝ)*X 0 1+(269294299/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((528921433/1000000000 : ℝ)*X 1 0+(-428826793/2000000000 : ℝ)*X 1 1+(1077177201/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2644607051/5000000000 : ℝ)*X 2 0+(1346471479/2500000000 : ℝ)*X 2 1+(-268016799/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4493396657/10000000000 : ℝ)*X 0 0+(1075464633/2500000000 : ℝ)*X 0 1+(4301858589/10000000000 : ℝ)*X 0 2+(4493396657/10000000000 : ℝ)*X 1 0+(1075464633/2500000000 : ℝ)*X 1 1+(4301858589/10000000000 : ℝ)*X 1 2+(4493396657/10000000000 : ℝ)*X 2 0+(1075464633/2500000000 : ℝ)*X 2 1+(4301858589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2092764147/10000000000 : ℝ)*X 0 0+(67996107/125000000 : ℝ)*X 0 1+(1054626157/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((671109109/1250000000 : ℝ)*X 1 0+(-1094253683/5000000000 : ℝ)*X 1 1+(1318282809/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2684436531/5000000000 : ℝ)*X 2 0+(5273131197/10000000000 : ℝ)*X 2 1+(-1094253581/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4238078471/10000000000 : ℝ)*X 0 0+(276844703/625000000 : ℝ)*X 0 1+(442951503/1000000000 : ℝ)*X 0 2+(4238078471/10000000000 : ℝ)*X 1 0+(276844703/625000000 : ℝ)*X 1 1+(442951503/1000000000 : ℝ)*X 1 2+(4238078471/10000000000 : ℝ)*X 2 0+(276844703/625000000 : ℝ)*X 2 1+(442951503/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1144_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62231/100000 : ℝ) ≤ (-104699839808884299954297293537817/168250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4232699/100000000000000 : ℝ)*(lower0) + (48148481/20000000000000 : ℝ)*(upper1) + (37521417/10000000000000 : ℝ)*(lower4) + (1961221462586039/50000000000000 : ℝ)*(major0) + (1961221462586039/50000000000000 : ℝ)*(major1) + (3922442925172079/100000000000000 : ℝ)*(major2) + (26290967127/100000000000000 : ℝ)*(sp2) + (3122510377/25000000000000 : ℝ)*(sp3) + (5242136544175079/100000000000000 : ℝ)*(sp4) + (5242120732384087/100000000000000 : ℝ)*(sp5) + (2621059126764577/50000000000000 : ℝ)*(sp6) + (2623471726120149/100000000000000 : ℝ)*(sp7) + (8000321201/100000000000000 : ℝ)*(sp12) + (23812112193/100000000000000 : ℝ)*(sp13) + (1311742108080829/50000000000000 : ℝ)*(f.failure) + (131053613612407/2500000000000 : ℝ)*(f.sum) + (33556993509087/13460000000000000000000000000 : ℝ)*base65 + (2769526409280220939/336500000000000000000000000000000 : ℝ)*base68 + (1732696025248395979/673000000000000000000000000000000 : ℝ)*base70 + (1755286164738220939/336500000000000000000000000000000 : ℝ)*base72 + (444577314483307/13460000000000000000000000000 : ℝ)*base73 + (7471270917009604021/673000000000000000000000000000000 : ℝ)*base75 + (5717808393191495939/336500000000000000000000000000000 : ℝ)*base78 + (6531822243383004061/336500000000000000000000000000000 : ℝ)*base79 + (16244738922639/3365000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (30153707/1250000000000000000000 : ℝ)*base89 + (30153707/1250000000000000000000 : ℝ)*base91 + (17653707/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (593/1000 : ℝ) ≤ (12472075053269060857974207711591/21031250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (177338919/100000000000000 : ℝ)*(lower1) + (50780989/20000000000000 : ℝ)*(lower2) + (55796571/100000000000000 : ℝ)*(lower3) + (180263821/50000000000000 : ℝ)*(upper4) + (249164466106753/6250000000000 : ℝ)*(major0) + (249164466106753/6250000000000 : ℝ)*(major1) + (249164466106753/6250000000000 : ℝ)*(major2) + (5287079353662437/100000000000000 : ℝ)*(sp0) + (5287073732740269/100000000000000 : ℝ)*(sp1) + (5287058062718121/100000000000000 : ℝ)*(sp2) + (1333204267716441/50000000000000 : ℝ)*(sp3) + (702615271/12500000000000 : ℝ)*(sp5) + (21290944317/100000000000000 : ℝ)*(sp6) + (1499551377/20000000000000 : ℝ)*(sp7) + (333302004148721/12500000000000 : ℝ)*(f.failure) + (5287079353662437/100000000000000 : ℝ)*(f.sum) + (8025432754837/1682500000000000000000000000 : ℝ)*base65 + (45094255987155947/42062500000000000000000000000000 : ℝ)*base67 + (918202789226906553/42062500000000000000000000000000 : ℝ)*base70 + (3226032327135468447/42062500000000000000000000000000 : ℝ)*base71 + (13614766023539/3365000000000000000000000000 : ℝ)*base73 + (202520334035344053/42062500000000000000000000000000 : ℝ)*base76 + (1196031598198969053/42062500000000000000000000000000 : ℝ)*base78 + (45080539463719053/42062500000000000000000000000000 : ℝ)*base80 + (77820897311/52578125000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2753943/312500000000000000000 : ℝ)*base89 + (2753943/312500000000000000000 : ℝ)*base91 + (2753943/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (39907/50000 : ℝ) ≤ (268583937613303087860429614209857/336500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3326719/20000000000000 : ℝ)*(upper0) + (71003641/100000000000000 : ℝ)*(upper1) + (256583681/100000000000000 : ℝ)*(upper2) + (111554011/100000000000000 : ℝ)*(lower5) + (111362963513891/2500000000000 : ℝ)*(major0) + (111362963513891/2500000000000 : ℝ)*(major1) + (4454518540555641/100000000000000 : ℝ)*(major2) + (179651791009/100000000000000 : ℝ)*(sp1) + (70160645749/100000000000000 : ℝ)*(sp3) + (2073271873/25000000000000 : ℝ)*(sp4) + (1180613163511259/20000000000000 : ℝ)*(sp8) + (5902894458852777/100000000000000 : ℝ)*(sp9) + (5903074110643787/100000000000000 : ℝ)*(sp10) + (297928716964211/10000000000000 : ℝ)*(sp11) + (1489678665143929/50000000000000 : ℝ)*(f.failure) + (5903074110643787/100000000000000 : ℝ)*(f.sum) + (11076386768831/13460000000000000000000000000 : ℝ)*base65 + (67899737324678241/16825000000000000000000000000000 : ℝ)*base68 + (2473061035232083741/673000000000000000000000000000000 : ℝ)*base70 + (11579623358521759/16825000000000000000000000000000 : ℝ)*base71 + (409743222999049/13460000000000000000000000000 : ℝ)*base74 + (829345577687083741/673000000000000000000000000000000 : ℝ)*base76 + (180728002057091991/16825000000000000000000000000000 : ℝ)*base78 + (437564483706541991/16825000000000000000000000000000 : ℝ)*base80 + (259302399601/168250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (498993/1250000000000000000000 : ℝ)*base90 + (498993/1250000000000000000000 : ℝ)*base92 + (12998993/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-83129/100000 : ℝ) ≤ (-223776105633357531234499059/269200000000000000000000000 : ℝ) := by norm_num
    linear_combination (2290941/3125000000000 : ℝ)*(lower0) + (114075253/100000000000000 : ℝ)*(lower2) + (66837/97656250000 : ℝ)*(upper3) + (198772183/100000000000000 : ℝ)*(upper5) + (1122376158353569/25000000000000 : ℝ)*(major0) + (1122376158353569/25000000000000 : ℝ)*(major1) + (4489504633414277/100000000000000 : ℝ)*(major2) + (18002474349/100000000000000 : ℝ)*(sp4) + (59335297833/20000000000000 : ℝ)*(sp7) + (8330667177/50000000000000 : ℝ)*(sp8) + (6003925976567579/100000000000000 : ℝ)*(sp12) + (3001980320188141/50000000000000 : ℝ)*(sp13) + (3001980320188141/50000000000000 : ℝ)*(sp14) + (750615182439801/25000000000000 : ℝ)*(sp15) + (300275740624837/10000000000000 : ℝ)*(f.failure) + (3001980320188141/50000000000000 : ℝ)*(f.sum) + (120316120937723/13460000000000000000000000000 : ℝ)*base65 + (3018056519186498969/168250000000000000000000000000000 : ℝ)*base68 + (719616296305949977/673000000000000000000000000000000 : ℝ)*base70 + (137882807283748969/168250000000000000000000000000000 : ℝ)*base72 + (40053301518037/13460000000000000000000000000 : ℝ)*base74 + (1117857746312050023/673000000000000000000000000000000 : ℝ)*base75 + (1260370690689113531/168250000000000000000000000000000 : ℝ)*base77 + (1454386949459363531/168250000000000000000000000000000 : ℝ)*base79 + (1752671697501/420625000000000000000000000 : ℝ)*base81 + (1731171/250000000000000000000 : ℝ)*base89 + (1731171/250000000000000000000 : ℝ)*base91 + (768829/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1144_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37378183/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14049/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11357/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62231/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(593/1000 : ℝ) else (39907/50000 : ℝ) ≤ X j i ∧ X j i ≤ (83129/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1144_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1144_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37378183/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (281/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2839/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62231/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(593/1000 : ℝ) else (39907/50000 : ℝ) ≤ X j i ∧ X j i ≤ (83129/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1144_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1144_s10 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1144_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (521/128 : ℝ) ≤ p) (hpb : p ≤ (8337/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37378183/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (281/2000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2839/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62231/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(593/1000 : ℝ) else (39907/50000 : ℝ) ≤ X j i ∧ X j i ≤ (83129/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1144_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
