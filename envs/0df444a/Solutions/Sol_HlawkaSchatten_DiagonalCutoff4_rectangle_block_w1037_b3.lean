-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1037_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:44:28.701994+00:00
-- url     : https://prove2.me/submissions/327ca90d-7de4-493b-9559-62c7210bb542

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
theorem support_rectangle_w1037_s9_0 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672516271/5000000000 : ℝ)*x 0 + (131598267/250000000 : ℝ)*x 1 + (-2284553593/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672516271/5000000000 : ℝ)^4115 ≤ (21716736466947/50000000000000 : ℝ)^3091 := by
    have hnat : (2672516271 : ℕ)^4115*50000000000000^3091 ≤ 21716736466947^3091*5000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672516271 5000000000 21716736466947 50000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131598267/250000000 : ℝ)^4115 ≤ (42558329509367/100000000000000 : ℝ)^3091 := by
    have hnat : (131598267 : ℕ)^4115*100000000000000^3091 ≤ 42558329509367^3091*250000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131598267 250000000 42558329509367 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2284553593/10000000000 : ℝ)^4115 ≤ (14008197538401/100000000000000 : ℝ)^3091 := by
    have hnat : (2284553593 : ℕ)^4115*100000000000000^3091 ≤ 14008197538401^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2284553593 10000000000 14008197538401 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672516271/5000000000 : ℝ), (131598267/250000000 : ℝ), (-2284553593/10000000000 : ℝ)] ![(21716736466947/50000000000000 : ℝ), (42558329509367/100000000000000 : ℝ), (14008197538401/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672516271/5000000000 : ℝ)|^4115 ≤ (21716736466947/50000000000000 : ℝ)^3091
        have hw : |(2672516271/5000000000 : ℝ)|=(2672516271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131598267/250000000 : ℝ)|^4115 ≤ (42558329509367/100000000000000 : ℝ)^3091
        have hw : |(131598267/250000000 : ℝ)|=(131598267/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2284553593/10000000000 : ℝ)|^4115 ≤ (14008197538401/100000000000000 : ℝ)^3091
        have hw : |(-2284553593/10000000000 : ℝ)|=(2284553593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_s9_1 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2218133873/10000000000 : ℝ)*x 0 + (5264258057/10000000000 : ℝ)*x 1 + (2697253663/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2218133873/10000000000 : ℝ)^4115 ≤ (2693727823443/20000000000000 : ℝ)^3091 := by
    have hnat : (2218133873 : ℕ)^4115*20000000000000^3091 ≤ 2693727823443^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2218133873 10000000000 2693727823443 20000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264258057/10000000000 : ℝ)^4115 ≤ (42561853200911/100000000000000 : ℝ)^3091 := by
    have hnat : (5264258057 : ℕ)^4115*100000000000000^3091 ≤ 42561853200911^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264258057 10000000000 42561853200911 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697253663/5000000000 : ℝ)^4115 ≤ (43969507674173/100000000000000 : ℝ)^3091 := by
    have hnat : (2697253663 : ℕ)^4115*100000000000000^3091 ≤ 43969507674173^3091*5000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697253663 5000000000 43969507674173 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2218133873/10000000000 : ℝ), (5264258057/10000000000 : ℝ), (2697253663/5000000000 : ℝ)] ![(2693727823443/20000000000000 : ℝ), (42561853200911/100000000000000 : ℝ), (43969507674173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2218133873/10000000000 : ℝ)|^4115 ≤ (2693727823443/20000000000000 : ℝ)^3091
        have hw : |(-2218133873/10000000000 : ℝ)|=(2218133873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264258057/10000000000 : ℝ)|^4115 ≤ (42561853200911/100000000000000 : ℝ)^3091
        have hw : |(5264258057/10000000000 : ℝ)|=(5264258057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697253663/5000000000 : ℝ)|^4115 ≤ (43969507674173/100000000000000 : ℝ)^3091
        have hw : |(2697253663/5000000000 : ℝ)|=(2697253663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_s9_2 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1328034251/2500000000 : ℝ)*x 0 + (-1076988461/5000000000 : ℝ)*x 1 + (1078901463/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328034251/2500000000 : ℝ)^4115 ≤ (10769493467207/25000000000000 : ℝ)^3091 := by
    have hnat : (1328034251 : ℕ)^4115*25000000000000^3091 ≤ 10769493467207^3091*2500000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328034251 2500000000 10769493467207 25000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076988461/5000000000 : ℝ)^4115 ≤ (12952518557439/100000000000000 : ℝ)^3091 := by
    have hnat : (1076988461 : ℕ)^4115*100000000000000^3091 ≤ 12952518557439^3091*5000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076988461 5000000000 12952518557439 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078901463/2000000000 : ℝ)^4115 ≤ (10992376888703/25000000000000 : ℝ)^3091 := by
    have hnat : (1078901463 : ℕ)^4115*25000000000000^3091 ≤ 10992376888703^3091*2000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078901463 2000000000 10992376888703 25000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328034251/2500000000 : ℝ), (-1076988461/5000000000 : ℝ), (1078901463/2000000000 : ℝ)] ![(10769493467207/25000000000000 : ℝ), (12952518557439/100000000000000 : ℝ), (10992376888703/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328034251/2500000000 : ℝ)|^4115 ≤ (10769493467207/25000000000000 : ℝ)^3091
        have hw : |(1328034251/2500000000 : ℝ)|=(1328034251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1076988461/5000000000 : ℝ)|^4115 ≤ (12952518557439/100000000000000 : ℝ)^3091
        have hw : |(-1076988461/5000000000 : ℝ)|=(1076988461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078901463/2000000000 : ℝ)|^4115 ≤ (10992376888703/25000000000000 : ℝ)^3091
        have hw : |(1078901463/2000000000 : ℝ)|=(1078901463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_s9_3 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656068529/5000000000 : ℝ)*x 0 + (5394507313/10000000000 : ℝ)*x 1 + (-2153976853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656068529/5000000000 : ℝ)^4115 ≤ (10769493612951/25000000000000 : ℝ)^3091 := by
    have hnat : (2656068529 : ℕ)^4115*25000000000000^3091 ≤ 10769493612951^3091*5000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656068529 5000000000 10769493612951 25000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394507313/10000000000 : ℝ)^4115 ≤ (4396950753311/10000000000000 : ℝ)^3091 := by
    have hnat : (5394507313 : ℕ)^4115*10000000000000^3091 ≤ 4396950753311^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394507313 10000000000 4396950753311 10000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2153976853/10000000000 : ℝ)^4115 ≤ (2590503601013/20000000000000 : ℝ)^3091 := by
    have hnat : (2153976853 : ℕ)^4115*20000000000000^3091 ≤ 2590503601013^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153976853 10000000000 2590503601013 20000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656068529/5000000000 : ℝ), (5394507313/10000000000 : ℝ), (-2153976853/10000000000 : ℝ)] ![(10769493612951/25000000000000 : ℝ), (4396950753311/10000000000000 : ℝ), (2590503601013/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656068529/5000000000 : ℝ)|^4115 ≤ (10769493612951/25000000000000 : ℝ)^3091
        have hw : |(2656068529/5000000000 : ℝ)|=(2656068529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394507313/10000000000 : ℝ)|^4115 ≤ (4396950753311/10000000000000 : ℝ)^3091
        have hw : |(5394507313/10000000000 : ℝ)|=(5394507313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2153976853/10000000000 : ℝ)|^4115 ≤ (2590503601013/20000000000000 : ℝ)^3091
        have hw : |(-2153976853/10000000000 : ℝ)|=(2153976853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_s9_4 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4379690739/10000000000 : ℝ)*x 0 + (450847709/1000000000 : ℝ)*x 1 + (4254675367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4379690739/10000000000 : ℝ)^4115 ≤ (16658245777359/50000000000000 : ℝ)^3091 := by
    have hnat : (4379690739 : ℕ)^4115*50000000000000^3091 ≤ 16658245777359^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379690739 10000000000 16658245777359 50000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450847709/1000000000 : ℝ)^4115 ≤ (17313519984611/50000000000000 : ℝ)^3091 := by
    have hnat : (450847709 : ℕ)^4115*50000000000000^3091 ≤ 17313519984611^3091*1000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450847709 1000000000 17313519984611 50000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4254675367/10000000000 : ℝ)^4115 ≤ (16028234231553/50000000000000 : ℝ)^3091 := by
    have hnat : (4254675367 : ℕ)^4115*50000000000000^3091 ≤ 16028234231553^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4254675367 10000000000 16028234231553 50000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4379690739/10000000000 : ℝ), (450847709/1000000000 : ℝ), (4254675367/10000000000 : ℝ)] ![(16658245777359/50000000000000 : ℝ), (17313519984611/50000000000000 : ℝ), (16028234231553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4379690739/10000000000 : ℝ)|^4115 ≤ (16658245777359/50000000000000 : ℝ)^3091
        have hw : |(4379690739/10000000000 : ℝ)|=(4379690739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(450847709/1000000000 : ℝ)|^4115 ≤ (17313519984611/50000000000000 : ℝ)^3091
        have hw : |(450847709/1000000000 : ℝ)|=(450847709/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4254675367/10000000000 : ℝ)|^4115 ≤ (16028234231553/50000000000000 : ℝ)^3091
        have hw : |(4254675367/10000000000 : ℝ)|=(4254675367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1037_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73714607/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2797/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11211/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (437/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2797/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11211/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2797/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11211/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2797/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11211/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2797/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11211/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2797/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11211/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2797/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11211/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11211/100000 : ℝ) ^ (8229/2048 : ℝ) ≤ (1898094855439319/12500000000000000000 : ℝ) := by
    have hpowers : (11211/100000 : ℝ)^8229 ≤ (1898094855439319/12500000000000000000 : ℝ)^2048 := by
      have hnat : (11211 : ℕ)^8229*12500000000000000000^2048 ≤ 1898094855439319^2048*100000^8229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11211 100000 1898094855439319 12500000000000000000 8229 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11211/100000 : ℝ)) (X := (1898094855439319/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8229 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2797/20000 : ℝ) ^ (8229/2048 : ℝ) ≤ (36916037115093529/100000000000000000000 : ℝ) := by
    have hpowers : (2797/20000 : ℝ)^8229 ≤ (36916037115093529/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2797 : ℕ)^8229*100000000000000000000^2048 ≤ 36916037115093529^2048*20000^8229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2797 20000 36916037115093529 100000000000000000000 8229 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2797/20000 : ℝ)) (X := (36916037115093529/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8229 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251898094855439319/6250000000000000000 : ℝ) ≤ (2500188934498547/2500000000000000 : ℝ) ^ (8229/2048 : ℝ) := by
    have hpowers : (6251898094855439319/6250000000000000000 : ℝ)^2048 ≤ (2500188934498547/2500000000000000 : ℝ)^8229 := by
      have hnat : (6251898094855439319 : ℕ)^2048*2500000000000000^8229 ≤ 2500188934498547^8229*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251898094855439319 6250000000000000000 2500188934498547 2500000000000000 2048 8229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500188934498547/2500000000000000 : ℝ)) (X := (6251898094855439319/6250000000000000000 : ℝ)) (by norm_num) 8229 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100052100795958608081/100000000000000000000 : ℝ) ≤ (5000648204872521/5000000000000000 : ℝ) ^ (8229/2048 : ℝ) := by
    have hpowers : (100052100795958608081/100000000000000000000 : ℝ)^2048 ≤ (5000648204872521/5000000000000000 : ℝ)^8229 := by
      have hnat : (100052100795958608081 : ℕ)^2048*5000000000000000^8229 ≤ 5000648204872521^8229*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100052100795958608081 100000000000000000000 5000648204872521 5000000000000000 2048 8229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000648204872521/5000000000000000 : ℝ)) (X := (100052100795958608081/100000000000000000000 : ℝ)) (by norm_num) 8229 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036916037115093529/50000000000000000000 : ℝ) ≤ (1250229635186987/1250000000000000 : ℝ) ^ (8229/2048 : ℝ) := by
    have hpowers : (50036916037115093529/50000000000000000000 : ℝ)^2048 ≤ (1250229635186987/1250000000000000 : ℝ)^8229 := by
      have hnat : (50036916037115093529 : ℕ)^2048*1250000000000000^8229 ≤ 1250229635186987^8229*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036916037115093529 50000000000000000000 1250229635186987 1250000000000000 2048 8229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250229635186987/1250000000000000 : ℝ)) (X := (50036916037115093529/50000000000000000000 : ℝ)) (by norm_num) 8229 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1898094855439319/12500000000000000000 : ℝ) ≤ ((6932493368799557281/6935000000000000000 : ℝ)+2*(270335875427/138700000000000 : ℝ)*(11211/100000 : ℝ))^(8229/2048 : ℝ) := by
    rw [show (6932493368799557281/6935000000000000000 : ℝ)+2*(270335875427/138700000000000 : ℝ)*(11211/100000 : ℝ)=(2500188934498547/2500000000000000 : ℝ) by norm_num, show 1+2*(1898094855439319/12500000000000000000 : ℝ)=(6251898094855439319/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36916037115093529/100000000000000000000 : ℝ)+(1898094855439319/12500000000000000000 : ℝ) ≤ ((6932493368799557281/6935000000000000000 : ℝ)+(270335875427/138700000000000 : ℝ)*((2797/20000 : ℝ)+(11211/100000 : ℝ)))^(8229/2048 : ℝ) := by
    rw [show (6932493368799557281/6935000000000000000 : ℝ)+(270335875427/138700000000000 : ℝ)*((2797/20000 : ℝ)+(11211/100000 : ℝ))=(5000648204872521/5000000000000000 : ℝ) by norm_num, show 1+(36916037115093529/100000000000000000000 : ℝ)+(1898094855439319/12500000000000000000 : ℝ)=(100052100795958608081/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36916037115093529/100000000000000000000 : ℝ) ≤ ((6932493368799557281/6935000000000000000 : ℝ)+2*(270335875427/138700000000000 : ℝ)*(2797/20000 : ℝ))^(8229/2048 : ℝ) := by
    rw [show (6932493368799557281/6935000000000000000 : ℝ)+2*(270335875427/138700000000000 : ℝ)*(2797/20000 : ℝ)=(1250229635186987/1250000000000000 : ℝ) by norm_num, show 1+2*(36916037115093529/100000000000000000000 : ℝ)=(50036916037115093529/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6932493368799557281/6935000000000000000 : ℝ)*(X 1 0+X 2 0)+(270335875427/138700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8229/2048 : ℝ)) (lo := (11211/100000 : ℝ)) (hi := (2797/20000 : ℝ)) (c := (6932493368799557281/6935000000000000000 : ℝ)) (alpha := (270335875427/138700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6932493368799557281/6935000000000000000 : ℝ)*(X 0 1+X 2 1)+(270335875427/138700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8229/2048 : ℝ)) (lo := (11211/100000 : ℝ)) (hi := (2797/20000 : ℝ)) (c := (6932493368799557281/6935000000000000000 : ℝ)) (alpha := (270335875427/138700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6932493368799557281/6935000000000000000 : ℝ)*(X 0 2+X 1 2)+(270335875427/138700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8229/2048 : ℝ)) (lo := (11211/100000 : ℝ)) (hi := (2797/20000 : ℝ)) (c := (6932493368799557281/6935000000000000000 : ℝ)) (alpha := (270335875427/138700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((2672516271/5000000000 : ℝ)*X 2 0+(131598267/250000000 : ℝ)*X 2 1+(-2284553593/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s9_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-2218133873/10000000000 : ℝ)*X 0 0+(5264258057/10000000000 : ℝ)*X 0 1+(2697253663/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s9_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1328034251/2500000000 : ℝ)*X 1 0+(-1076988461/5000000000 : ℝ)*X 1 1+(1078901463/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s9_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2656068529/5000000000 : ℝ)*X 2 0+(5394507313/10000000000 : ℝ)*X 2 1+(-2153976853/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s9_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((4379690739/10000000000 : ℝ)*X 0 0+(450847709/1000000000 : ℝ)*X 0 1+(4254675367/10000000000 : ℝ)*X 0 2+(4379690739/10000000000 : ℝ)*X 1 0+(450847709/1000000000 : ℝ)*X 1 1+(4254675367/10000000000 : ℝ)*X 1 2+(4379690739/10000000000 : ℝ)*X 2 0+(450847709/1000000000 : ℝ)*X 2 1+(4254675367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_s9_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (35591295631038219540471/6935000000000000000000000000 : ℝ) := by norm_num
    linear_combination (483719259/50000000000000 : ℝ)*(base19) + (1162033573/100000000000000 : ℝ)*(base23) + (1248909/400000000000 : ℝ)*(lower1) + (124880531/100000000000000 : ℝ)*(upper3) + (7581787/20000000000000 : ℝ)*(lower4) + (111118277/100000000000000 : ℝ)*(upper5) + (1452204221232967/25000000000000 : ℝ)*(major0) + (1452204221232967/25000000000000 : ℝ)*(major1) + (1452204221232967/25000000000000 : ℝ)*(major2) + (7296985153/100000000000000 : ℝ)*(sp0) + (479847612460323/6250000000000 : ℝ)*(sp1) + (153551216638533/2000000000000 : ℝ)*(sp2) + (3838776670173221/50000000000000 : ℝ)*(sp3) + (985017949856917/25000000000000 : ℝ)*(sp4) + (985017949856917/25000000000000 : ℝ)*(f.failure) + (479847612460323/6250000000000 : ℝ)*(f.sum) + (176584336029/108359375000000000000000000 : ℝ)*base65 + (7481875182011467273/173375000000000000000000000000000 : ℝ)*base68 + (2141947374709032727/173375000000000000000000000000000 : ℝ)*base69 + (17585812779157967273/173375000000000000000000000000000 : ℝ)*base72 + (3674764341367/866875000000000000000000000 : ℝ)*base73 + (2720046583170217273/173375000000000000000000000000000 : ℝ)*base76 + (1432776304930282727/173375000000000000000000000000000 : ℝ)*base77 + (3861259470679782727/173375000000000000000000000000000 : ℝ)*base79 + (57680517856701/6935000000000000000000000000 : ℝ)*base81 + (7113381/1250000000000000000000 : ℝ)*base90 + (7113381/1250000000000000000000 : ℝ)*base92 + (7113381/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1037_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73714607/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2797/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (437/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1037_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1037_box_0 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-130478523/625000000 : ℝ)*x 0 + (2688878313/5000000000 : ℝ)*x 1 + (134443917/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (130478523/625000000 : ℝ)^4115 ≤ (12424321389547/100000000000000 : ℝ)^3091 := by
    have hnat : (130478523 : ℕ)^4115*100000000000000^3091 ≤ 12424321389547^3091*625000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130478523 625000000 12424321389547 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2688878313/5000000000 : ℝ)^4115 ≤ (547347987627/1250000000000 : ℝ)^3091 := by
    have hnat : (2688878313 : ℕ)^4115*1250000000000^3091 ≤ 547347987627^3091*5000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2688878313 5000000000 547347987627 1250000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (134443917/250000000 : ℝ)^4115 ≤ (5473479949439/12500000000000 : ℝ)^3091 := by
    have hnat : (134443917 : ℕ)^4115*12500000000000^3091 ≤ 5473479949439^3091*250000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134443917 250000000 5473479949439 12500000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-130478523/625000000 : ℝ), (2688878313/5000000000 : ℝ), (134443917/250000000 : ℝ)] ![(12424321389547/100000000000000 : ℝ), (547347987627/1250000000000 : ℝ), (5473479949439/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-130478523/625000000 : ℝ)|^4115 ≤ (12424321389547/100000000000000 : ℝ)^3091
        have hw : |(-130478523/625000000 : ℝ)|=(130478523/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2688878313/5000000000 : ℝ)|^4115 ≤ (547347987627/1250000000000 : ℝ)^3091
        have hw : |(2688878313/5000000000 : ℝ)|=(2688878313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(134443917/250000000 : ℝ)|^4115 ≤ (5473479949439/12500000000000 : ℝ)^3091
        have hw : |(134443917/250000000 : ℝ)|=(134443917/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_box_1 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294863111/10000000000 : ℝ)*x 0 + (-439958303/2000000000 : ℝ)*x 1 + (1344439233/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294863111/10000000000 : ℝ)^4115 ≤ (5361448504257/12500000000000 : ℝ)^3091 := by
    have hnat : (5294863111 : ℕ)^4115*12500000000000^3091 ≤ 5361448504257^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294863111 10000000000 5361448504257 12500000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (439958303/2000000000 : ℝ)^4115 ≤ (2664113925333/20000000000000 : ℝ)^3091 := by
    have hnat : (439958303 : ℕ)^4115*20000000000000^3091 ≤ 2664113925333^3091*2000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439958303 2000000000 2664113925333 20000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1344439233/2500000000 : ℝ)^4115 ≤ (21893921163577/50000000000000 : ℝ)^3091 := by
    have hnat : (1344439233 : ℕ)^4115*50000000000000^3091 ≤ 21893921163577^3091*2500000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344439233 2500000000 21893921163577 50000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294863111/10000000000 : ℝ), (-439958303/2000000000 : ℝ), (1344439233/2500000000 : ℝ)] ![(5361448504257/12500000000000 : ℝ), (2664113925333/20000000000000 : ℝ), (21893921163577/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294863111/10000000000 : ℝ)|^4115 ≤ (5361448504257/12500000000000 : ℝ)^3091
        have hw : |(5294863111/10000000000 : ℝ)|=(5294863111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-439958303/2000000000 : ℝ)|^4115 ≤ (2664113925333/20000000000000 : ℝ)^3091
        have hw : |(-439958303/2000000000 : ℝ)|=(439958303/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1344439233/2500000000 : ℝ)|^4115 ≤ (21893921163577/50000000000000 : ℝ)^3091
        have hw : |(1344439233/2500000000 : ℝ)|=(1344439233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_box_2 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294863763/10000000000 : ℝ)*x 0 + (336109771/625000000 : ℝ)*x 1 + (-2199791443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294863763/10000000000 : ℝ)^4115 ≤ (42891595065359/100000000000000 : ℝ)^3091 := by
    have hnat : (5294863763 : ℕ)^4115*100000000000000^3091 ≤ 42891595065359^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294863763 10000000000 42891595065359 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336109771/625000000 : ℝ)^4115 ≤ (10946958966651/25000000000000 : ℝ)^3091 := by
    have hnat : (336109771 : ℕ)^4115*25000000000000^3091 ≤ 10946958966651^3091*625000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336109771 625000000 10946958966651 25000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2199791443/10000000000 : ℝ)^4115 ≤ (6660284523121/50000000000000 : ℝ)^3091 := by
    have hnat : (2199791443 : ℕ)^4115*50000000000000^3091 ≤ 6660284523121^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199791443 10000000000 6660284523121 50000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294863763/10000000000 : ℝ), (336109771/625000000 : ℝ), (-2199791443/10000000000 : ℝ)] ![(42891595065359/100000000000000 : ℝ), (10946958966651/25000000000000 : ℝ), (6660284523121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294863763/10000000000 : ℝ)|^4115 ≤ (42891595065359/100000000000000 : ℝ)^3091
        have hw : |(5294863763/10000000000 : ℝ)|=(5294863763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336109771/625000000 : ℝ)|^4115 ≤ (10946958966651/25000000000000 : ℝ)^3091
        have hw : |(336109771/625000000 : ℝ)|=(336109771/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2199791443/10000000000 : ℝ)|^4115 ≤ (6660284523121/50000000000000 : ℝ)^3091
        have hw : |(-2199791443/10000000000 : ℝ)|=(2199791443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_box_3 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (448840677/1000000000 : ℝ)*x 0 + (4327501509/10000000000 : ℝ)*x 1 + (1081875477/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (448840677/1000000000 : ℝ)^4115 ≤ (268921685311/781250000000 : ℝ)^3091 := by
    have hnat : (448840677 : ℕ)^4115*781250000000^3091 ≤ 268921685311^3091*1000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448840677 1000000000 268921685311 781250000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4327501509/10000000000 : ℝ)^4115 ≤ (32789010119561/100000000000000 : ℝ)^3091 := by
    have hnat : (4327501509 : ℕ)^4115*100000000000000^3091 ≤ 32789010119561^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4327501509 10000000000 32789010119561 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081875477/2500000000 : ℝ)^4115 ≤ (32789014144273/100000000000000 : ℝ)^3091 := by
    have hnat : (1081875477 : ℕ)^4115*100000000000000^3091 ≤ 32789014144273^3091*2500000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081875477 2500000000 32789014144273 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(448840677/1000000000 : ℝ), (4327501509/10000000000 : ℝ), (1081875477/2500000000 : ℝ)] ![(268921685311/781250000000 : ℝ), (32789010119561/100000000000000 : ℝ), (32789014144273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(448840677/1000000000 : ℝ)|^4115 ≤ (268921685311/781250000000 : ℝ)^3091
        have hw : |(448840677/1000000000 : ℝ)|=(448840677/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4327501509/10000000000 : ℝ)|^4115 ≤ (32789010119561/100000000000000 : ℝ)^3091
        have hw : |(4327501509/10000000000 : ℝ)|=(4327501509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081875477/2500000000 : ℝ)|^4115 ≤ (32789014144273/100000000000000 : ℝ)^3091
        have hw : |(1081875477/2500000000 : ℝ)|=(1081875477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_box_4 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2349995343/10000000000 : ℝ)*x 0 + (5279644167/10000000000 : ℝ)*x 1 + (527964383/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2349995343/10000000000 : ℝ)^4115 ≤ (3636229917109/25000000000000 : ℝ)^3091 := by
    have hnat : (2349995343 : ℕ)^4115*25000000000000^3091 ≤ 3636229917109^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2349995343 10000000000 3636229917109 25000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5279644167/10000000000 : ℝ)^4115 ≤ (8545508395723/20000000000000 : ℝ)^3091 := by
    have hnat : (5279644167 : ℕ)^4115*20000000000000^3091 ≤ 8545508395723^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279644167 10000000000 8545508395723 20000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527964383/1000000000 : ℝ)^4115 ≤ (42727538347801/100000000000000 : ℝ)^3091 := by
    have hnat : (527964383 : ℕ)^4115*100000000000000^3091 ≤ 42727538347801^3091*1000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527964383 1000000000 42727538347801 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2349995343/10000000000 : ℝ), (5279644167/10000000000 : ℝ), (527964383/1000000000 : ℝ)] ![(3636229917109/25000000000000 : ℝ), (8545508395723/20000000000000 : ℝ), (42727538347801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2349995343/10000000000 : ℝ)|^4115 ≤ (3636229917109/25000000000000 : ℝ)^3091
        have hw : |(-2349995343/10000000000 : ℝ)|=(2349995343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5279644167/10000000000 : ℝ)|^4115 ≤ (8545508395723/20000000000000 : ℝ)^3091
        have hw : |(5279644167/10000000000 : ℝ)|=(5279644167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(527964383/1000000000 : ℝ)|^4115 ≤ (42727538347801/100000000000000 : ℝ)^3091
        have hw : |(527964383/1000000000 : ℝ)|=(527964383/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_box_5 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5364345967/10000000000 : ℝ)*x 0 + (-139878569/625000000 : ℝ)*x 1 + (5279643983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364345967/10000000000 : ℝ)^4115 ≤ (8728505916423/20000000000000 : ℝ)^3091 := by
    have hnat : (5364345967 : ℕ)^4115*20000000000000^3091 ≤ 8728505916423^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364345967 10000000000 8728505916423 20000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (139878569/625000000 : ℝ)^4115 ≤ (13629930416823/100000000000000 : ℝ)^3091 := by
    have hnat : (139878569 : ℕ)^4115*100000000000000^3091 ≤ 13629930416823^3091*625000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139878569 625000000 13629930416823 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5279643983/10000000000 : ℝ)^4115 ≤ (10681884999053/25000000000000 : ℝ)^3091 := by
    have hnat : (5279643983 : ℕ)^4115*25000000000000^3091 ≤ 10681884999053^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279643983 10000000000 10681884999053 25000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364345967/10000000000 : ℝ), (-139878569/625000000 : ℝ), (5279643983/10000000000 : ℝ)] ![(8728505916423/20000000000000 : ℝ), (13629930416823/100000000000000 : ℝ), (10681884999053/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364345967/10000000000 : ℝ)|^4115 ≤ (8728505916423/20000000000000 : ℝ)^3091
        have hw : |(5364345967/10000000000 : ℝ)|=(5364345967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-139878569/625000000 : ℝ)|^4115 ≤ (13629930416823/100000000000000 : ℝ)^3091
        have hw : |(-139878569/625000000 : ℝ)|=(139878569/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5279643983/10000000000 : ℝ)|^4115 ≤ (10681884999053/25000000000000 : ℝ)^3091
        have hw : |(5279643983/10000000000 : ℝ)|=(5279643983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_box_6 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2682173153/5000000000 : ℝ)*x 0 + (5279643767/10000000000 : ℝ)*x 1 + (-279757117/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2682173153/5000000000 : ℝ)^4115 ≤ (8728506650757/20000000000000 : ℝ)^3091 := by
    have hnat : (2682173153 : ℕ)^4115*20000000000000^3091 ≤ 8728506650757^3091*5000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2682173153 5000000000 8728506650757 20000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5279643767/10000000000 : ℝ)^4115 ≤ (42727537669043/100000000000000 : ℝ)^3091 := by
    have hnat : (5279643767 : ℕ)^4115*100000000000000^3091 ≤ 42727537669043^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279643767 10000000000 42727537669043 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (279757117/1250000000 : ℝ)^4115 ≤ (13629929054743/100000000000000 : ℝ)^3091 := by
    have hnat : (279757117 : ℕ)^4115*100000000000000^3091 ≤ 13629929054743^3091*1250000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279757117 1250000000 13629929054743 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2682173153/5000000000 : ℝ), (5279643767/10000000000 : ℝ), (-279757117/1250000000 : ℝ)] ![(8728506650757/20000000000000 : ℝ), (42727537669043/100000000000000 : ℝ), (13629929054743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2682173153/5000000000 : ℝ)|^4115 ≤ (8728506650757/20000000000000 : ℝ)^3091
        have hw : |(2682173153/5000000000 : ℝ)|=(2682173153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5279643767/10000000000 : ℝ)|^4115 ≤ (42727537669043/100000000000000 : ℝ)^3091
        have hw : |(5279643767/10000000000 : ℝ)|=(5279643767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-279757117/1250000000 : ℝ)|^4115 ≤ (13629929054743/100000000000000 : ℝ)^3091
        have hw : |(-279757117/1250000000 : ℝ)|=(279757117/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_box_7 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (427063899/1000000000 : ℝ)*x 0 + (4436363837/10000000000 : ℝ)*x 1 + (4436363947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427063899/1000000000 : ℝ)^4115 ≤ (32216690093337/100000000000000 : ℝ)^3091 := by
    have hnat : (427063899 : ℕ)^4115*100000000000000^3091 ≤ 32216690093337^3091*1000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427063899 1000000000 32216690093337 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4436363837/10000000000 : ℝ)^4115 ≤ (33891654385751/100000000000000 : ℝ)^3091 := by
    have hnat : (4436363837 : ℕ)^4115*100000000000000^3091 ≤ 33891654385751^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4436363837 10000000000 33891654385751 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4436363947/10000000000 : ℝ)^4115 ≤ (33891655504491/100000000000000 : ℝ)^3091 := by
    have hnat : (4436363947 : ℕ)^4115*100000000000000^3091 ≤ 33891655504491^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4436363947 10000000000 33891655504491 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(427063899/1000000000 : ℝ), (4436363837/10000000000 : ℝ), (4436363947/10000000000 : ℝ)] ![(32216690093337/100000000000000 : ℝ), (33891654385751/100000000000000 : ℝ), (33891655504491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(427063899/1000000000 : ℝ)|^4115 ≤ (32216690093337/100000000000000 : ℝ)^3091
        have hw : |(427063899/1000000000 : ℝ)|=(427063899/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4436363837/10000000000 : ℝ)|^4115 ≤ (33891654385751/100000000000000 : ℝ)^3091
        have hw : |(4436363837/10000000000 : ℝ)|=(4436363837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4436363947/10000000000 : ℝ)|^4115 ≤ (33891655504491/100000000000000 : ℝ)^3091
        have hw : |(4436363947/10000000000 : ℝ)|=(4436363947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_box_8 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2295266969/10000000000 : ℝ)*x 0 + (5213126421/10000000000 : ℝ)*x 1 + (336709583/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2295266969/10000000000 : ℝ)^4115 ≤ (2819143815877/20000000000000 : ℝ)^3091 := by
    have hnat : (2295266969 : ℕ)^4115*20000000000000^3091 ≤ 2819143815877^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2295266969 10000000000 2819143815877 20000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5213126421/10000000000 : ℝ)^4115 ≤ (42012384358891/100000000000000 : ℝ)^3091 := by
    have hnat : (5213126421 : ℕ)^4115*100000000000000^3091 ≤ 42012384358891^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213126421 10000000000 42012384358891 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336709583/625000000 : ℝ)^4115 ≤ (43891896540913/100000000000000 : ℝ)^3091 := by
    have hnat : (336709583 : ℕ)^4115*100000000000000^3091 ≤ 43891896540913^3091*625000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336709583 625000000 43891896540913 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2295266969/10000000000 : ℝ), (5213126421/10000000000 : ℝ), (336709583/625000000 : ℝ)] ![(2819143815877/20000000000000 : ℝ), (42012384358891/100000000000000 : ℝ), (43891896540913/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2295266969/10000000000 : ℝ)|^4115 ≤ (2819143815877/20000000000000 : ℝ)^3091
        have hw : |(-2295266969/10000000000 : ℝ)|=(2295266969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5213126421/10000000000 : ℝ)|^4115 ≤ (42012384358891/100000000000000 : ℝ)^3091
        have hw : |(5213126421/10000000000 : ℝ)|=(5213126421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336709583/625000000 : ℝ)|^4115 ≤ (43891896540913/100000000000000 : ℝ)^3091
        have hw : |(336709583/625000000 : ℝ)|=(336709583/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_box_9 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288063249/10000000000 : ℝ)*x 0 + (-137248603/625000000 : ℝ)*x 1 + (1077470623/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288063249/10000000000 : ℝ)^4115 ≤ (8563654503403/20000000000000 : ℝ)^3091 := by
    have hnat : (5288063249 : ℕ)^4115*20000000000000^3091 ≤ 8563654503403^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288063249 10000000000 8563654503403 20000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (137248603/625000000 : ℝ)^4115 ≤ (13289833236127/100000000000000 : ℝ)^3091 := by
    have hnat : (137248603 : ℕ)^4115*100000000000000^3091 ≤ 13289833236127^3091*625000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137248603 625000000 13289833236127 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077470623/2000000000 : ℝ)^4115 ≤ (43891894230661/100000000000000 : ℝ)^3091 := by
    have hnat : (1077470623 : ℕ)^4115*100000000000000^3091 ≤ 43891894230661^3091*2000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077470623 2000000000 43891894230661 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288063249/10000000000 : ℝ), (-137248603/625000000 : ℝ), (1077470623/2000000000 : ℝ)] ![(8563654503403/20000000000000 : ℝ), (13289833236127/100000000000000 : ℝ), (43891894230661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288063249/10000000000 : ℝ)|^4115 ≤ (8563654503403/20000000000000 : ℝ)^3091
        have hw : |(5288063249/10000000000 : ℝ)|=(5288063249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-137248603/625000000 : ℝ)|^4115 ≤ (13289833236127/100000000000000 : ℝ)^3091
        have hw : |(-137248603/625000000 : ℝ)|=(137248603/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077470623/2000000000 : ℝ)|^4115 ≤ (43891894230661/100000000000000 : ℝ)^3091
        have hw : |(1077470623/2000000000 : ℝ)|=(1077470623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_box_10 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5288063553/10000000000 : ℝ)*x 0 + (168354789/312500000 : ℝ)*x 1 + (-1097988531/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288063553/10000000000 : ℝ)^4115 ≤ (42818275794019/100000000000000 : ℝ)^3091 := by
    have hnat : (5288063553 : ℕ)^4115*100000000000000^3091 ≤ 42818275794019^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288063553 10000000000 42818275794019 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168354789/312500000 : ℝ)^4115 ≤ (43891895673213/100000000000000 : ℝ)^3091 := by
    have hnat : (168354789 : ℕ)^4115*100000000000000^3091 ≤ 43891895673213^3091*312500000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168354789 312500000 43891895673213 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097988531/5000000000 : ℝ)^4115 ≤ (3322457128711/25000000000000 : ℝ)^3091 := by
    have hnat : (1097988531 : ℕ)^4115*25000000000000^3091 ≤ 3322457128711^3091*5000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097988531 5000000000 3322457128711 25000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288063553/10000000000 : ℝ), (168354789/312500000 : ℝ), (-1097988531/5000000000 : ℝ)] ![(42818275794019/100000000000000 : ℝ), (43891895673213/100000000000000 : ℝ), (3322457128711/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288063553/10000000000 : ℝ)|^4115 ≤ (42818275794019/100000000000000 : ℝ)^3091
        have hw : |(5288063553/10000000000 : ℝ)|=(5288063553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168354789/312500000 : ℝ)|^4115 ≤ (43891895673213/100000000000000 : ℝ)^3091
        have hw : |(168354789/312500000 : ℝ)|=(168354789/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1097988531/5000000000 : ℝ)|^4115 ≤ (3322457128711/25000000000000 : ℝ)^3091
        have hw : |(-1097988531/5000000000 : ℝ)|=(1097988531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_box_11 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4509433309/10000000000 : ℝ)*x 0 + (4316847833/10000000000 : ℝ)*x 1 + (4316848009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4509433309/10000000000 : ℝ)^4115 ≤ (8659204373701/25000000000000 : ℝ)^3091 := by
    have hnat : (4509433309 : ℕ)^4115*25000000000000^3091 ≤ 8659204373701^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509433309 10000000000 8659204373701 25000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4316847833/10000000000 : ℝ)^4115 ≤ (1307263614517/4000000000000 : ℝ)^3091 := by
    have hnat : (4316847833 : ℕ)^4115*4000000000000^3091 ≤ 1307263614517^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316847833 10000000000 1307263614517 4000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4316848009/10000000000 : ℝ)^4115 ≤ (8170398034197/25000000000000 : ℝ)^3091 := by
    have hnat : (4316848009 : ℕ)^4115*25000000000000^3091 ≤ 8170398034197^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316848009 10000000000 8170398034197 25000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4509433309/10000000000 : ℝ), (4316847833/10000000000 : ℝ), (4316848009/10000000000 : ℝ)] ![(8659204373701/25000000000000 : ℝ), (1307263614517/4000000000000 : ℝ), (8170398034197/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4509433309/10000000000 : ℝ)|^4115 ≤ (8659204373701/25000000000000 : ℝ)^3091
        have hw : |(4509433309/10000000000 : ℝ)|=(4509433309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4316847833/10000000000 : ℝ)|^4115 ≤ (1307263614517/4000000000000 : ℝ)^3091
        have hw : |(4316847833/10000000000 : ℝ)|=(4316847833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4316848009/10000000000 : ℝ)|^4115 ≤ (8170398034197/25000000000000 : ℝ)^3091
        have hw : |(4316848009/10000000000 : ℝ)|=(4316848009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_box_12 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-535693187/2500000000 : ℝ)*x 0 + (2721457749/5000000000 : ℝ)*x 1 + (527165911/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535693187/2500000000 : ℝ)^4115 ≤ (12862901832511/100000000000000 : ℝ)^3091 := by
    have hnat : (535693187 : ℕ)^4115*100000000000000^3091 ≤ 12862901832511^3091*2500000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535693187 2500000000 12862901832511 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2721457749/5000000000 : ℝ)^4115 ≤ (44495565042299/100000000000000 : ℝ)^3091 := by
    have hnat : (2721457749 : ℕ)^4115*100000000000000^3091 ≤ 44495565042299^3091*5000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721457749 5000000000 44495565042299 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527165911/1000000000 : ℝ)^4115 ≤ (21320766552407/50000000000000 : ℝ)^3091 := by
    have hnat : (527165911 : ℕ)^4115*50000000000000^3091 ≤ 21320766552407^3091*1000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527165911 1000000000 21320766552407 50000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-535693187/2500000000 : ℝ), (2721457749/5000000000 : ℝ), (527165911/1000000000 : ℝ)] ![(12862901832511/100000000000000 : ℝ), (44495565042299/100000000000000 : ℝ), (21320766552407/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-535693187/2500000000 : ℝ)|^4115 ≤ (12862901832511/100000000000000 : ℝ)^3091
        have hw : |(-535693187/2500000000 : ℝ)|=(535693187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2721457749/5000000000 : ℝ)|^4115 ≤ (44495565042299/100000000000000 : ℝ)^3091
        have hw : |(2721457749/5000000000 : ℝ)|=(2721457749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(527165911/1000000000 : ℝ)|^4115 ≤ (21320766552407/50000000000000 : ℝ)^3091
        have hw : |(527165911/1000000000 : ℝ)|=(527165911/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_box_13 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369998371/10000000000 : ℝ)*x 0 + (-280139029/1250000000 : ℝ)*x 1 + (5271659133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369998371/10000000000 : ℝ)^4115 ≤ (21851880403069/50000000000000 : ℝ)^3091 := by
    have hnat : (5369998371 : ℕ)^4115*50000000000000^3091 ≤ 21851880403069^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369998371 10000000000 21851880403069 50000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (280139029/1250000000 : ℝ)^4115 ≤ (426709557141/3125000000000 : ℝ)^3091 := by
    have hnat : (280139029 : ℕ)^4115*3125000000000^3091 ≤ 426709557141^3091*1250000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280139029 1250000000 426709557141 3125000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5271659133/10000000000 : ℝ)^4115 ≤ (4264153335249/10000000000000 : ℝ)^3091 := by
    have hnat : (5271659133 : ℕ)^4115*10000000000000^3091 ≤ 4264153335249^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271659133 10000000000 4264153335249 10000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369998371/10000000000 : ℝ), (-280139029/1250000000 : ℝ), (5271659133/10000000000 : ℝ)] ![(21851880403069/50000000000000 : ℝ), (426709557141/3125000000000 : ℝ), (4264153335249/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369998371/10000000000 : ℝ)|^4115 ≤ (21851880403069/50000000000000 : ℝ)^3091
        have hw : |(5369998371/10000000000 : ℝ)|=(5369998371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-280139029/1250000000 : ℝ)|^4115 ≤ (426709557141/3125000000000 : ℝ)^3091
        have hw : |(-280139029/1250000000 : ℝ)|=(280139029/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5271659133/10000000000 : ℝ)|^4115 ≤ (4264153335249/10000000000000 : ℝ)^3091
        have hw : |(5271659133/10000000000 : ℝ)|=(5271659133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_box_14 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369998579/10000000000 : ℝ)*x 0 + (5271659081/10000000000 : ℝ)*x 1 + (-1120556011/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369998579/10000000000 : ℝ)^4115 ≤ (43703763059749/100000000000000 : ℝ)^3091 := by
    have hnat : (5369998579 : ℕ)^4115*100000000000000^3091 ≤ 43703763059749^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369998579 10000000000 43703763059749 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5271659081/10000000000 : ℝ)^4115 ≤ (42641532792527/100000000000000 : ℝ)^3091 := by
    have hnat : (5271659081 : ℕ)^4115*100000000000000^3091 ≤ 42641532792527^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271659081 10000000000 42641532792527 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1120556011/5000000000 : ℝ)^4115 ≤ (13654704125143/100000000000000 : ℝ)^3091 := by
    have hnat : (1120556011 : ℕ)^4115*100000000000000^3091 ≤ 13654704125143^3091*5000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120556011 5000000000 13654704125143 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369998579/10000000000 : ℝ), (5271659081/10000000000 : ℝ), (-1120556011/5000000000 : ℝ)] ![(43703763059749/100000000000000 : ℝ), (42641532792527/100000000000000 : ℝ), (13654704125143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369998579/10000000000 : ℝ)|^4115 ≤ (43703763059749/100000000000000 : ℝ)^3091
        have hw : |(5369998579/10000000000 : ℝ)|=(5369998579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5271659081/10000000000 : ℝ)|^4115 ≤ (42641532792527/100000000000000 : ℝ)^3091
        have hw : |(5271659081/10000000000 : ℝ)|=(5271659081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1120556011/5000000000 : ℝ)|^4115 ≤ (13654704125143/100000000000000 : ℝ)^3091
        have hw : |(-1120556011/5000000000 : ℝ)|=(1120556011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1037_box_15 (p : ℝ) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4252685349/10000000000 : ℝ)*x 0 + (4445219047/10000000000 : ℝ)*x 1 + (88904383/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4252685349/10000000000 : ℝ)^4115 ≤ (32036509249107/100000000000000 : ℝ)^3091 := by
    have hnat : (4252685349 : ℕ)^4115*100000000000000^3091 ≤ 32036509249107^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4252685349 10000000000 32036509249107 100000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4445219047/10000000000 : ℝ)^4115 ≤ (16990872423997/50000000000000 : ℝ)^3091 := by
    have hnat : (4445219047 : ℕ)^4115*50000000000000^3091 ≤ 16990872423997^3091*10000000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4445219047 10000000000 16990872423997 50000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (88904383/200000000 : ℝ)^4115 ≤ (16990872948117/50000000000000 : ℝ)^3091 := by
    have hnat : (88904383 : ℕ)^4115*50000000000000^3091 ≤ 16990872948117^3091*200000000^4115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88904383 200000000 16990872948117 50000000000000 4115 3091 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4115/1024 : ℝ)) 4115 3091 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4252685349/10000000000 : ℝ), (4445219047/10000000000 : ℝ), (88904383/200000000 : ℝ)] ![(32036509249107/100000000000000 : ℝ), (16990872423997/50000000000000 : ℝ), (16990872948117/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4252685349/10000000000 : ℝ)|^4115 ≤ (32036509249107/100000000000000 : ℝ)^3091
        have hw : |(4252685349/10000000000 : ℝ)|=(4252685349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4445219047/10000000000 : ℝ)|^4115 ≤ (16990872423997/50000000000000 : ℝ)^3091
        have hw : |(4445219047/10000000000 : ℝ)|=(4445219047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(88904383/200000000 : ℝ)|^4115 ≤ (16990872948117/50000000000000 : ℝ)^3091
        have hw : |(88904383/200000000 : ℝ)|=(88904383/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1037_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73714607/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (437/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62223/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59219/100000 : ℝ) ∧ (1987/2500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (41443/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (437/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11211/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (437/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11211/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (437/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11211/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (437/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11211/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (437/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11211/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (437/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11211/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11211/100000 : ℝ) ^ (8229/2048 : ℝ) ≤ (1898094855439319/12500000000000000000 : ℝ) := by
    have hpowers : (11211/100000 : ℝ)^8229 ≤ (1898094855439319/12500000000000000000 : ℝ)^2048 := by
      have hnat : (11211 : ℕ)^8229*12500000000000000000^2048 ≤ 1898094855439319^2048*100000^8229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11211 100000 1898094855439319 12500000000000000000 8229 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11211/100000 : ℝ)) (X := (1898094855439319/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8229 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (437/3125 : ℝ) ^ (8229/2048 : ℝ) ≤ (36905431817711973/100000000000000000000 : ℝ) := by
    have hpowers : (437/3125 : ℝ)^8229 ≤ (36905431817711973/100000000000000000000 : ℝ)^2048 := by
      have hnat : (437 : ℕ)^8229*100000000000000000000^2048 ≤ 36905431817711973^2048*3125^8229 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        437 3125 36905431817711973 100000000000000000000 8229 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (437/3125 : ℝ)) (X := (36905431817711973/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8229 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251898094855439319/6250000000000000000 : ℝ) ≤ (2500188934498547/2500000000000000 : ℝ) ^ (8229/2048 : ℝ) := by
    have hpowers : (6251898094855439319/6250000000000000000 : ℝ)^2048 ≤ (2500188934498547/2500000000000000 : ℝ)^8229 := by
      have hnat : (6251898094855439319 : ℕ)^2048*2500000000000000^8229 ≤ 2500188934498547^8229*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251898094855439319 6250000000000000000 2500188934498547 2500000000000000 2048 8229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500188934498547/2500000000000000 : ℝ)) (X := (6251898094855439319/6250000000000000000 : ℝ)) (by norm_num) 8229 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (4002083607626449061/4000000000000000000 : ℝ) ≤ (5000648072953977/5000000000000000 : ℝ) ^ (8229/2048 : ℝ) := by
    have hpowers : (4002083607626449061/4000000000000000000 : ℝ)^2048 ≤ (5000648072953977/5000000000000000 : ℝ)^8229 := by
      have hnat : (4002083607626449061 : ℕ)^2048*5000000000000000^8229 ≤ 5000648072953977^8229*4000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4002083607626449061 4000000000000000000 5000648072953977 5000000000000000 2048 8229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000648072953977/5000000000000000 : ℝ)) (X := (4002083607626449061/4000000000000000000 : ℝ)) (by norm_num) 8229 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036905431817711973/50000000000000000000 : ℝ) ≤ (250045913845543/250000000000000 : ℝ) ^ (8229/2048 : ℝ) := by
    have hpowers : (50036905431817711973/50000000000000000000 : ℝ)^2048 ≤ (250045913845543/250000000000000 : ℝ)^8229 := by
      have hnat : (50036905431817711973 : ℕ)^2048*250000000000000^8229 ≤ 250045913845543^8229*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036905431817711973 50000000000000000000 250045913845543 250000000000000 2048 8229 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250045913845543/250000000000000 : ℝ)) (X := (50036905431817711973/50000000000000000000 : ℝ)) (by norm_num) 8229 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1898094855439319/12500000000000000000 : ℝ) ≤ ((3464997329401927759/3466250000000000000 : ℝ)+2*(270203956883/138650000000000 : ℝ)*(11211/100000 : ℝ))^(8229/2048 : ℝ) := by
    rw [show (3464997329401927759/3466250000000000000 : ℝ)+2*(270203956883/138650000000000 : ℝ)*(11211/100000 : ℝ)=(2500188934498547/2500000000000000 : ℝ) by norm_num, show 1+2*(1898094855439319/12500000000000000000 : ℝ)=(6251898094855439319/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36905431817711973/100000000000000000000 : ℝ)+(1898094855439319/12500000000000000000 : ℝ) ≤ ((3464997329401927759/3466250000000000000 : ℝ)+(270203956883/138650000000000 : ℝ)*((437/3125 : ℝ)+(11211/100000 : ℝ)))^(8229/2048 : ℝ) := by
    rw [show (3464997329401927759/3466250000000000000 : ℝ)+(270203956883/138650000000000 : ℝ)*((437/3125 : ℝ)+(11211/100000 : ℝ))=(5000648072953977/5000000000000000 : ℝ) by norm_num, show 1+(36905431817711973/100000000000000000000 : ℝ)+(1898094855439319/12500000000000000000 : ℝ)=(4002083607626449061/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36905431817711973/100000000000000000000 : ℝ) ≤ ((3464997329401927759/3466250000000000000 : ℝ)+2*(270203956883/138650000000000 : ℝ)*(437/3125 : ℝ))^(8229/2048 : ℝ) := by
    rw [show (3464997329401927759/3466250000000000000 : ℝ)+2*(270203956883/138650000000000 : ℝ)*(437/3125 : ℝ)=(250045913845543/250000000000000 : ℝ) by norm_num, show 1+2*(36905431817711973/100000000000000000000 : ℝ)=(50036905431817711973/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3464997329401927759/3466250000000000000 : ℝ)*(X 1 0+X 2 0)+(270203956883/138650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8229/2048 : ℝ)) (lo := (11211/100000 : ℝ)) (hi := (437/3125 : ℝ)) (c := (3464997329401927759/3466250000000000000 : ℝ)) (alpha := (270203956883/138650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3464997329401927759/3466250000000000000 : ℝ)*(X 0 1+X 2 1)+(270203956883/138650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8229/2048 : ℝ)) (lo := (11211/100000 : ℝ)) (hi := (437/3125 : ℝ)) (c := (3464997329401927759/3466250000000000000 : ℝ)) (alpha := (270203956883/138650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3464997329401927759/3466250000000000000 : ℝ)*(X 0 2+X 1 2)+(270203956883/138650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8229/2048 : ℝ)) (lo := (11211/100000 : ℝ)) (hi := (437/3125 : ℝ)) (c := (3464997329401927759/3466250000000000000 : ℝ)) (alpha := (270203956883/138650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-130478523/625000000 : ℝ)*X 0 0+(2688878313/5000000000 : ℝ)*X 0 1+(134443917/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5294863111/10000000000 : ℝ)*X 1 0+(-439958303/2000000000 : ℝ)*X 1 1+(1344439233/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5294863763/10000000000 : ℝ)*X 2 0+(336109771/625000000 : ℝ)*X 2 1+(-2199791443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((448840677/1000000000 : ℝ)*X 0 0+(4327501509/10000000000 : ℝ)*X 0 1+(1081875477/2500000000 : ℝ)*X 0 2+(448840677/1000000000 : ℝ)*X 1 0+(4327501509/10000000000 : ℝ)*X 1 1+(1081875477/2500000000 : ℝ)*X 1 2+(448840677/1000000000 : ℝ)*X 2 0+(4327501509/10000000000 : ℝ)*X 2 1+(1081875477/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2349995343/10000000000 : ℝ)*X 0 0+(5279644167/10000000000 : ℝ)*X 0 1+(527964383/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5364345967/10000000000 : ℝ)*X 1 0+(-139878569/625000000 : ℝ)*X 1 1+(5279643983/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2682173153/5000000000 : ℝ)*X 2 0+(5279643767/10000000000 : ℝ)*X 2 1+(-279757117/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((427063899/1000000000 : ℝ)*X 0 0+(4436363837/10000000000 : ℝ)*X 0 1+(4436363947/10000000000 : ℝ)*X 0 2+(427063899/1000000000 : ℝ)*X 1 0+(4436363837/10000000000 : ℝ)*X 1 1+(4436363947/10000000000 : ℝ)*X 1 2+(427063899/1000000000 : ℝ)*X 2 0+(4436363837/10000000000 : ℝ)*X 2 1+(4436363947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2295266969/10000000000 : ℝ)*X 0 0+(5213126421/10000000000 : ℝ)*X 0 1+(336709583/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5288063249/10000000000 : ℝ)*X 1 0+(-137248603/625000000 : ℝ)*X 1 1+(1077470623/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5288063553/10000000000 : ℝ)*X 2 0+(168354789/312500000 : ℝ)*X 2 1+(-1097988531/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4509433309/10000000000 : ℝ)*X 0 0+(4316847833/10000000000 : ℝ)*X 0 1+(4316848009/10000000000 : ℝ)*X 0 2+(4509433309/10000000000 : ℝ)*X 1 0+(4316847833/10000000000 : ℝ)*X 1 1+(4316848009/10000000000 : ℝ)*X 1 2+(4509433309/10000000000 : ℝ)*X 2 0+(4316847833/10000000000 : ℝ)*X 2 1+(4316848009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-535693187/2500000000 : ℝ)*X 0 0+(2721457749/5000000000 : ℝ)*X 0 1+(527165911/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5369998371/10000000000 : ℝ)*X 1 0+(-280139029/1250000000 : ℝ)*X 1 1+(5271659133/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5369998579/10000000000 : ℝ)*X 2 0+(5271659081/10000000000 : ℝ)*X 2 1+(-1120556011/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4252685349/10000000000 : ℝ)*X 0 0+(4445219047/10000000000 : ℝ)*X 0 1+(88904383/200000000 : ℝ)*X 0 2+(4252685349/10000000000 : ℝ)*X 1 0+(4445219047/10000000000 : ℝ)*X 1 1+(88904383/200000000 : ℝ)*X 1 2+(4252685349/10000000000 : ℝ)*X 2 0+(4445219047/10000000000 : ℝ)*X 2 1+(88904383/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1037_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62223/100000 : ℝ) ≤ (-53918256843068338069264895387997/86656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (113108141/100000000000000 : ℝ)*(upper0) + (92273853/100000000000000 : ℝ)*(lower2) + (77416517/100000000000000 : ℝ)*(upper4) + (2407789/100000000000000 : ℝ)*(upper5) + (1915961496426963/50000000000000 : ℝ)*(major0) + (1915961496426963/50000000000000 : ℝ)*(major1) + (1915961496426963/50000000000000 : ℝ)*(major2) + (128683791/5000000000000 : ℝ)*(sp1) + (2963071239/100000000000000 : ℝ)*(sp2) + (508541545731351/10000000000000 : ℝ)*(sp4) + (635677806473833/12500000000000 : ℝ)*(sp5) + (1017084412479049/20000000000000 : ℝ)*(sp6) + (1299580622078717/50000000000000 : ℝ)*(sp7) + (4784076487/50000000000000 : ℝ)*(sp8) + (1299580622078717/50000000000000 : ℝ)*(f.failure) + (5085425025466483/100000000000000 : ℝ)*(f.sum) + (921492913691/866562500000000000000000000 : ℝ)*base65 + (272048772882634083/173312500000000000000000000000000 : ℝ)*base68 + (2004625462046634083/173312500000000000000000000000000 : ℝ)*base70 + (10371731137509083/173312500000000000000000000000000 : ℝ)*base72 + (38823877927043/6932500000000000000000000000 : ℝ)*base73 + (1961265825367884083/173312500000000000000000000000000 : ℝ)*base76 + (920088908280446583/173312500000000000000000000000000 : ℝ)*base78 + (2077165358141071583/173312500000000000000000000000000 : ℝ)*base80 + (53484043229451/13865000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (3280781/2500000000000000000000 : ℝ)*base90 + (3280781/2500000000000000000000 : ℝ)*base92 + (3280781/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (59219/100000 : ℝ) ≤ (51319377336991391185113243493731/86656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (112009917/100000000000000 : ℝ)*(upper0) + (26850987/100000000000000 : ℝ)*(lower1) + (83833599/50000000000000 : ℝ)*(upper4) + (4809349/5000000000000 : ℝ)*(upper5) + (1947176434000703/50000000000000 : ℝ)*(major0) + (1947176434000703/50000000000000 : ℝ)*(major1) + (1947176434000703/50000000000000 : ℝ)*(major2) + (256372911807199/5000000000000 : ℝ)*(sp0) + (1025489560634497/20000000000000 : ℝ)*(sp1) + (2563659890935883/50000000000000 : ℝ)*(sp2) + (2641504961111337/100000000000000 : ℝ)*(sp3) + (5216485747/50000000000000 : ℝ)*(sp5) + (486006789/25000000000000 : ℝ)*(sp7) + (138454272213/100000000000000 : ℝ)*(sp10) + (1320753452569247/50000000000000 : ℝ)*(f.failure) + (256372911807199/5000000000000 : ℝ)*(f.sum) + (31655631549573/6932500000000000000000000000 : ℝ)*base65 + (9263952717457872923/173312500000000000000000000000000 : ℝ)*base68 + (1562462649379060423/173312500000000000000000000000000 : ℝ)*base70 + (916847649373752077/173312500000000000000000000000000 : ℝ)*base71 + (75888987331107/6932500000000000000000000000 : ℝ)*base74 + (1566145578479435423/173312500000000000000000000000000 : ℝ)*base76 + (391766183496372923/173312500000000000000000000000000 : ℝ)*base78 + (685450705569627077/173312500000000000000000000000000 : ℝ)*base79 + (6280272982791/3466250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (32890929/2500000000000000000000 : ℝ)*base89 + (32890929/2500000000000000000000 : ℝ)*base91 + (32890929/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (1987/2500 : ℝ) ≤ (17219225541144386051506997763549/21664062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (87396023/50000000000000 : ℝ)*(upper0) + (109633/100000000000 : ℝ)*(lower3) + (22493431/6250000000000 : ℝ)*(upper4) + (1090662675598687/25000000000000 : ℝ)*(major0) + (1090662675598687/25000000000000 : ℝ)*(major1) + (1090662675598687/25000000000000 : ℝ)*(major2) + (22597708823/25000000000000 : ℝ)*(sp1) + (363038528323/100000000000000 : ℝ)*(sp2) + (131647068547/100000000000000 : ℝ)*(sp3) + (4612518407/50000000000000 : ℝ)*(sp4) + (2869824239260683/50000000000000 : ℝ)*(sp8) + (717445914090361/12500000000000 : ℝ)*(sp9) + (5739294665029857/100000000000000 : ℝ)*(sp10) + (739754438383619/25000000000000 : ℝ)*(sp11) + (2959149400603023/100000000000000 : ℝ)*(f.failure) + (286982885177909/5000000000000 : ℝ)*(f.sum) + (44546918725199/6932500000000000000000000000 : ℝ)*base65 + (1342646264129441317/86656250000000000000000000000000 : ℝ)*base68 + (1137288861136597567/86656250000000000000000000000000 : ℝ)*base70 + (87608396538089933/86656250000000000000000000000000 : ℝ)*base71 + (463997175104887/13865000000000000000000000000 : ℝ)*base74 + (827464742408722567/86656250000000000000000000000000 : ℝ)*base76 + (477278120273097567/86656250000000000000000000000000 : ℝ)*base78 + (5134000621189441317/86656250000000000000000000000000 : ℝ)*base80 + (18409258857463/13865000000000000000000000000 : ℝ)*base81 + (3456961/5000000000000000000000 : ℝ)*base89 + (3456961/5000000000000000000000 : ℝ)*base91 + (3456961/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-41443/50000 : ℝ) ≤ (-14364745443490082291719383719343/17331250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5154999/6250000000000 : ℝ)*(lower1) + (77049883/50000000000000 : ℝ)*(lower2) + (53218347/100000000000000 : ℝ)*(upper5) + (879402719440691/20000000000000 : ℝ)*(major0) + (879402719440691/20000000000000 : ℝ)*(major1) + (879402719440691/20000000000000 : ℝ)*(major2) + (1037509961/50000000000000 : ℝ)*(sp0) + (114047585313/100000000000000 : ℝ)*(sp5) + (56295664783/100000000000000 : ℝ)*(sp6) + (20485480843/25000000000000 : ℝ)*(sp7) + (5839195486410387/100000000000000 : ℝ)*(sp12) + (5839083513844997/100000000000000 : ℝ)*(sp13) + (5839141265765527/100000000000000 : ℝ)*(sp14) + (11929502088697/400000000000 : ℝ)*(sp15) + (2982457464097621/100000000000000 : ℝ)*(f.failure) + (5839197561430309/100000000000000 : ℝ)*(f.sum) + (823364592407/693250000000000000000000000 : ℝ)*base66 + (42592161813966469/69325000000000000000000000000000 : ℝ)*base67 + (260766572022183531/69325000000000000000000000000000 : ℝ)*base70 + (1388622537779733531/69325000000000000000000000000000 : ℝ)*base72 + (78617510877/43328125000000000000000000 : ℝ)*base74 + (215377744065933531/69325000000000000000000000000000 : ℝ)*base76 + (981063994397958531/69325000000000000000000000000000 : ℝ)*base78 + (450008920474783531/69325000000000000000000000000000 : ℝ)*base80 + (245763588843/138650000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (8350053/5000000000000000000000 : ℝ)*base90 + (8350053/5000000000000000000000 : ℝ)*base92 + (8350053/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1037_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73714607/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (437/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59219/100000 : ℝ) else (1987/2500 : ℝ) ≤ X j i ∧ X j i ≤ (41443/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1037_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1037_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73714607/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2797/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59219/100000 : ℝ) else (1987/2500 : ℝ) ≤ X j i ∧ X j i ≤ (41443/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1037_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1037_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8229/2048 : ℝ) ≤ p) (hpb : p ≤ (4115/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (73714607/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2797/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62223/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(59219/100000 : ℝ) else (1987/2500 : ℝ) ≤ X j i ∧ X j i ≤ (41443/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1037_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
