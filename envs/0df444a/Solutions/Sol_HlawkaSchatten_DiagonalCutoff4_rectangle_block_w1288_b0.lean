-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1288_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:24:34.221133+00:00
-- url     : https://prove2.me/submissions/1dbd118b-b56a-40c6-b359-af5c36b286bf

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
theorem support_rectangle_w1288_s0_0 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-920752283/5000000000 : ℝ)*x 0 + (602056807/1000000000 : ℝ)*x 1 + (2398931247/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (920752283/5000000000 : ℝ)^531 ≤ (672447789401/6250000000000 : ℝ)^403 := by
    have hnat : (920752283 : ℕ)^531*6250000000000^403 ≤ 672447789401^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      920752283 5000000000 672447789401 6250000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (602056807/1000000000 : ℝ)^531 ≤ (25622198953893/50000000000000 : ℝ)^403 := by
    have hnat : (602056807 : ℕ)^531*50000000000000^403 ≤ 25622198953893^403*1000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      602056807 1000000000 25622198953893 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2398931247/5000000000 : ℝ)^531 ≤ (3799643744063/10000000000000 : ℝ)^403 := by
    have hnat : (2398931247 : ℕ)^531*10000000000000^403 ≤ 3799643744063^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2398931247 5000000000 3799643744063 10000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-920752283/5000000000 : ℝ), (602056807/1000000000 : ℝ), (2398931247/5000000000 : ℝ)] ![(672447789401/6250000000000 : ℝ), (25622198953893/50000000000000 : ℝ), (3799643744063/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-920752283/5000000000 : ℝ)|^531 ≤ (672447789401/6250000000000 : ℝ)^403
        have hw : |(-920752283/5000000000 : ℝ)|=(920752283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(602056807/1000000000 : ℝ)|^531 ≤ (25622198953893/50000000000000 : ℝ)^403
        have hw : |(602056807/1000000000 : ℝ)|=(602056807/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2398931247/5000000000 : ℝ)|^531 ≤ (3799643744063/10000000000000 : ℝ)^403
        have hw : |(2398931247/5000000000 : ℝ)|=(2398931247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s0_1 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5507867747/10000000000 : ℝ)*x 0 + (-507851781/2000000000 : ℝ)*x 1 + (1199465637/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5507867747/10000000000 : ℝ)^531 ≤ (45573799435969/100000000000000 : ℝ)^403 := by
    have hnat : (5507867747 : ℕ)^531*100000000000000^403 ≤ 45573799435969^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5507867747 10000000000 45573799435969 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (507851781/2000000000 : ℝ)^531 ≤ (16429762548493/100000000000000 : ℝ)^403 := by
    have hnat : (507851781 : ℕ)^531*100000000000000^403 ≤ 16429762548493^403*2000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507851781 2000000000 16429762548493 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1199465637/2500000000 : ℝ)^531 ≤ (3799643800411/10000000000000 : ℝ)^403 := by
    have hnat : (1199465637 : ℕ)^531*10000000000000^403 ≤ 3799643800411^403*2500000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1199465637 2500000000 3799643800411 10000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5507867747/10000000000 : ℝ), (-507851781/2000000000 : ℝ), (1199465637/2500000000 : ℝ)] ![(45573799435969/100000000000000 : ℝ), (16429762548493/100000000000000 : ℝ), (3799643800411/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5507867747/10000000000 : ℝ)|^531 ≤ (45573799435969/100000000000000 : ℝ)^403
        have hw : |(5507867747/10000000000 : ℝ)|=(5507867747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-507851781/2000000000 : ℝ)|^531 ≤ (16429762548493/100000000000000 : ℝ)^403
        have hw : |(-507851781/2000000000 : ℝ)|=(507851781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1199465637/2500000000 : ℝ)|^531 ≤ (3799643800411/10000000000000 : ℝ)^403
        have hw : |(1199465637/2500000000 : ℝ)|=(1199465637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s0_2 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2753933701/5000000000 : ℝ)*x 0 + (1199465763/2500000000 : ℝ)*x 1 + (-2539258729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2753933701/5000000000 : ℝ)^531 ≤ (45573795674649/100000000000000 : ℝ)^403 := by
    have hnat : (2753933701 : ℕ)^531*100000000000000^403 ≤ 45573795674649^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2753933701 5000000000 45573795674649 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1199465763/2500000000 : ℝ)^531 ≤ (18998221631627/50000000000000 : ℝ)^403 := by
    have hnat : (1199465763 : ℕ)^531*50000000000000^403 ≤ 18998221631627^403*2500000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1199465763 2500000000 18998221631627 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2539258729/10000000000 : ℝ)^531 ≤ (8214880524013/50000000000000 : ℝ)^403 := by
    have hnat : (2539258729 : ℕ)^531*50000000000000^403 ≤ 8214880524013^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539258729 10000000000 8214880524013 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2753933701/5000000000 : ℝ), (1199465763/2500000000 : ℝ), (-2539258729/10000000000 : ℝ)] ![(45573795674649/100000000000000 : ℝ), (18998221631627/50000000000000 : ℝ), (8214880524013/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2753933701/5000000000 : ℝ)|^531 ≤ (45573795674649/100000000000000 : ℝ)^403
        have hw : |(2753933701/5000000000 : ℝ)|=(2753933701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1199465763/2500000000 : ℝ)|^531 ≤ (18998221631627/50000000000000 : ℝ)^403
        have hw : |(1199465763/2500000000 : ℝ)|=(1199465763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2539258729/10000000000 : ℝ)|^531 ≤ (8214880524013/50000000000000 : ℝ)^403
        have hw : |(-2539258729/10000000000 : ℝ)|=(2539258729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s0_3 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2093473921/5000000000 : ℝ)*x 0 + (3109697547/10000000000 : ℝ)*x 1 + (5618805379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2093473921/5000000000 : ℝ)^531 ≤ (793862827077/2500000000000 : ℝ)^403 := by
    have hnat : (2093473921 : ℕ)^531*2500000000000^403 ≤ 793862827077^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2093473921 5000000000 793862827077 2500000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3109697547/10000000000 : ℝ)^531 ≤ (2145835237659/10000000000000 : ℝ)^403 := by
    have hnat : (3109697547 : ℕ)^531*10000000000000^403 ≤ 2145835237659^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3109697547 10000000000 2145835237659 10000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5618805379/10000000000 : ℝ)^531 ≤ (46787134529943/100000000000000 : ℝ)^403 := by
    have hnat : (5618805379 : ℕ)^531*100000000000000^403 ≤ 46787134529943^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5618805379 10000000000 46787134529943 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2093473921/5000000000 : ℝ), (3109697547/10000000000 : ℝ), (5618805379/10000000000 : ℝ)] ![(793862827077/2500000000000 : ℝ), (2145835237659/10000000000000 : ℝ), (46787134529943/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2093473921/5000000000 : ℝ)|^531 ≤ (793862827077/2500000000000 : ℝ)^403
        have hw : |(2093473921/5000000000 : ℝ)|=(2093473921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3109697547/10000000000 : ℝ)|^531 ≤ (2145835237659/10000000000000 : ℝ)^403
        have hw : |(3109697547/10000000000 : ℝ)|=(3109697547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5618805379/10000000000 : ℝ)|^531 ≤ (46787134529943/100000000000000 : ℝ)^403
        have hw : |(5618805379/10000000000 : ℝ)|=(5618805379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s0_4 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1846250453/10000000000 : ℝ)*x 0 + (482942621/1000000000 : ℝ)*x 1 + (748485271/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1846250453/10000000000 : ℝ)^531 ≤ (10795714870031/100000000000000 : ℝ)^403 := by
    have hnat : (1846250453 : ℕ)^531*100000000000000^403 ≤ 10795714870031^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1846250453 10000000000 10795714870031 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (482942621/1000000000 : ℝ)^531 ≤ (299422987637/781250000000 : ℝ)^403 := by
    have hnat : (482942621 : ℕ)^531*781250000000^403 ≤ 299422987637^403*1000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482942621 1000000000 299422987637 781250000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (748485271/1250000000 : ℝ)^531 ≤ (50878142700863/100000000000000 : ℝ)^403 := by
    have hnat : (748485271 : ℕ)^531*100000000000000^403 ≤ 50878142700863^403*1250000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748485271 1250000000 50878142700863 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1846250453/10000000000 : ℝ), (482942621/1000000000 : ℝ), (748485271/1250000000 : ℝ)] ![(10795714870031/100000000000000 : ℝ), (299422987637/781250000000 : ℝ), (50878142700863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1846250453/10000000000 : ℝ)|^531 ≤ (10795714870031/100000000000000 : ℝ)^403
        have hw : |(-1846250453/10000000000 : ℝ)|=(1846250453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(482942621/1000000000 : ℝ)|^531 ≤ (299422987637/781250000000 : ℝ)^403
        have hw : |(482942621/1000000000 : ℝ)|=(482942621/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(748485271/1250000000 : ℝ)|^531 ≤ (50878142700863/100000000000000 : ℝ)^403
        have hw : |(748485271/1250000000 : ℝ)|=(748485271/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s0_5 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5175025107/10000000000 : ℝ)*x 0 + (-674618527/5000000000 : ℝ)*x 1 + (2993942381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5175025107/10000000000 : ℝ)^531 ≤ (41980339607373/100000000000000 : ℝ)^403 := by
    have hnat : (5175025107 : ℕ)^531*100000000000000^403 ≤ 41980339607373^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175025107 10000000000 41980339607373 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674618527/5000000000 : ℝ)^531 ≤ (1428297726057/20000000000000 : ℝ)^403 := by
    have hnat : (674618527 : ℕ)^531*20000000000000^403 ≤ 1428297726057^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674618527 5000000000 1428297726057 20000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2993942381/5000000000 : ℝ)^531 ≤ (50878171742259/100000000000000 : ℝ)^403 := by
    have hnat : (2993942381 : ℕ)^531*100000000000000^403 ≤ 50878171742259^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2993942381 5000000000 50878171742259 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5175025107/10000000000 : ℝ), (-674618527/5000000000 : ℝ), (2993942381/5000000000 : ℝ)] ![(41980339607373/100000000000000 : ℝ), (1428297726057/20000000000000 : ℝ), (50878171742259/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5175025107/10000000000 : ℝ)|^531 ≤ (41980339607373/100000000000000 : ℝ)^403
        have hw : |(5175025107/10000000000 : ℝ)|=(5175025107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-674618527/5000000000 : ℝ)|^531 ≤ (1428297726057/20000000000000 : ℝ)^403
        have hw : |(-674618527/5000000000 : ℝ)|=(674618527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2993942381/5000000000 : ℝ)|^531 ≤ (50878171742259/100000000000000 : ℝ)^403
        have hw : |(2993942381/5000000000 : ℝ)|=(2993942381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s0_6 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (41400211/80000000 : ℝ)*x 0 + (374242661/625000000 : ℝ)*x 1 + (-1349238621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (41400211/80000000 : ℝ)^531 ≤ (8396070632117/20000000000000 : ℝ)^403 := by
    have hnat : (41400211 : ℕ)^531*20000000000000^403 ≤ 8396070632117^403*80000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41400211 80000000 8396070632117 20000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (374242661/625000000 : ℝ)^531 ≤ (50878147268669/100000000000000 : ℝ)^403 := by
    have hnat : (374242661 : ℕ)^531*100000000000000^403 ≤ 50878147268669^403*625000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      374242661 625000000 50878147268669 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349238621/10000000000 : ℝ)^531 ≤ (3570749779373/50000000000000 : ℝ)^403 := by
    have hnat : (1349238621 : ℕ)^531*50000000000000^403 ≤ 3570749779373^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349238621 10000000000 3570749779373 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(41400211/80000000 : ℝ), (374242661/625000000 : ℝ), (-1349238621/10000000000 : ℝ)] ![(8396070632117/20000000000000 : ℝ), (50878147268669/100000000000000 : ℝ), (3570749779373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(41400211/80000000 : ℝ)|^531 ≤ (8396070632117/20000000000000 : ℝ)^403
        have hw : |(41400211/80000000 : ℝ)|=(41400211/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(374242661/625000000 : ℝ)|^531 ≤ (50878147268669/100000000000000 : ℝ)^403
        have hw : |(374242661/625000000 : ℝ)|=(374242661/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1349238621/10000000000 : ℝ)|^531 ≤ (3570749779373/50000000000000 : ℝ)^403
        have hw : |(-1349238621/10000000000 : ℝ)|=(1349238621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s0_7 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4196690583/10000000000 : ℝ)*x 0 + (5554041833/10000000000 : ℝ)*x 1 + (397095571/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4196690583/10000000000 : ℝ)^531 ≤ (248843035843/781250000000 : ℝ)^403 := by
    have hnat : (4196690583 : ℕ)^531*781250000000^403 ≤ 248843035843^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4196690583 10000000000 248843035843 781250000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5554041833/10000000000 : ℝ)^531 ≤ (46077875677477/100000000000000 : ℝ)^403 := by
    have hnat : (5554041833 : ℕ)^531*100000000000000^403 ≤ 46077875677477^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5554041833 10000000000 46077875677477 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (397095571/1250000000 : ℝ)^531 ≤ (11035107863689/50000000000000 : ℝ)^403 := by
    have hnat : (397095571 : ℕ)^531*50000000000000^403 ≤ 11035107863689^403*1250000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397095571 1250000000 11035107863689 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4196690583/10000000000 : ℝ), (5554041833/10000000000 : ℝ), (397095571/1250000000 : ℝ)] ![(248843035843/781250000000 : ℝ), (46077875677477/100000000000000 : ℝ), (11035107863689/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4196690583/10000000000 : ℝ)|^531 ≤ (248843035843/781250000000 : ℝ)^403
        have hw : |(4196690583/10000000000 : ℝ)|=(4196690583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5554041833/10000000000 : ℝ)|^531 ≤ (46077875677477/100000000000000 : ℝ)^403
        have hw : |(5554041833/10000000000 : ℝ)|=(5554041833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(397095571/1250000000 : ℝ)|^531 ≤ (11035107863689/50000000000000 : ℝ)^403
        have hw : |(397095571/1250000000 : ℝ)|=(397095571/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1288_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152604817/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1001/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5453/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4247/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4247 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4247*1^1024 ≤ 0^1024*1^4247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4247 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4247/1024 : ℝ) ≤ (2236450851788538461/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4247 ≤ (2236450851788538461/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4247*100000000000000000000^1024 ≤ 2236450851788538461^1024*5^4247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2236450851788538461 100000000000000000000 4247 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2236450851788538461/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4247/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4247 := by
      have hnat : (1 : ℕ)^1024*1^4247 ≤ 1^4247*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102236450851788538461/100000000000000000000 : ℝ) ≤ (1256683960529843/1250000000000000 : ℝ) ^ (4247/1024 : ℝ) := by
    have hpowers : (102236450851788538461/100000000000000000000 : ℝ)^1024 ≤ (1256683960529843/1250000000000000 : ℝ)^4247 := by
      have hnat : (102236450851788538461 : ℕ)^1024*1250000000000000^4247 ≤ 1256683960529843^4247*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102236450851788538461 100000000000000000000 1256683960529843 1250000000000000 1024 4247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1256683960529843/1250000000000000 : ℝ)) (X := (102236450851788538461/100000000000000000000 : ℝ)) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52236450851788538461/50000000000000000000 : ℝ) ≤ (631683960529843/625000000000000 : ℝ) ^ (4247/1024 : ℝ) := by
    have hpowers : (52236450851788538461/50000000000000000000 : ℝ)^1024 ≤ (631683960529843/625000000000000 : ℝ)^4247 := by
      have hnat : (52236450851788538461 : ℕ)^1024*625000000000000^4247 ≤ 631683960529843^4247*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52236450851788538461 50000000000000000000 631683960529843 625000000000000 1024 4247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (631683960529843/625000000000000 : ℝ)) (X := (52236450851788538461/50000000000000000000 : ℝ)) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(6683960529843/500000000000000 : ℝ)*(0 : ℝ))^(4247/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(6683960529843/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2236450851788538461/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(6683960529843/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4247/1024 : ℝ) := by
    rw [show (1 : ℝ)+(6683960529843/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1256683960529843/1250000000000000 : ℝ) by norm_num, show 1+(2236450851788538461/100000000000000000000 : ℝ)+(0 : ℝ)=(102236450851788538461/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2236450851788538461/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(6683960529843/500000000000000 : ℝ)*(2/5 : ℝ))^(4247/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(6683960529843/500000000000000 : ℝ)*(2/5 : ℝ)=(631683960529843/625000000000000 : ℝ) by norm_num, show 1+2*(2236450851788538461/100000000000000000000 : ℝ)=(52236450851788538461/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(6683960529843/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4247/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6683960529843/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(6683960529843/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4247/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6683960529843/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(6683960529843/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4247/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6683960529843/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-920752283/5000000000 : ℝ)*X 0 0+(602056807/1000000000 : ℝ)*X 0 1+(2398931247/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5507867747/10000000000 : ℝ)*X 1 0+(-507851781/2000000000 : ℝ)*X 1 1+(1199465637/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2753933701/5000000000 : ℝ)*X 2 0+(1199465763/2500000000 : ℝ)*X 2 1+(-2539258729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2093473921/5000000000 : ℝ)*X 0 0+(3109697547/10000000000 : ℝ)*X 0 1+(5618805379/10000000000 : ℝ)*X 0 2+(2093473921/5000000000 : ℝ)*X 1 0+(3109697547/10000000000 : ℝ)*X 1 1+(5618805379/10000000000 : ℝ)*X 1 2+(2093473921/5000000000 : ℝ)*X 2 0+(3109697547/10000000000 : ℝ)*X 2 1+(5618805379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1846250453/10000000000 : ℝ)*X 0 0+(482942621/1000000000 : ℝ)*X 0 1+(748485271/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5175025107/10000000000 : ℝ)*X 1 0+(-674618527/5000000000 : ℝ)*X 1 1+(2993942381/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((41400211/80000000 : ℝ)*X 2 0+(374242661/625000000 : ℝ)*X 2 1+(-1349238621/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4196690583/10000000000 : ℝ)*X 0 0+(5554041833/10000000000 : ℝ)*X 0 1+(397095571/1250000000 : ℝ)*X 0 2+(4196690583/10000000000 : ℝ)*X 1 0+(5554041833/10000000000 : ℝ)*X 1 1+(397095571/1250000000 : ℝ)*X 1 2+(4196690583/10000000000 : ℝ)*X 2 0+(5554041833/10000000000 : ℝ)*X 2 1+(397095571/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7184050840344070129047/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27911297/20000000000000 : ℝ)*(base1) + (741616431/50000000000000 : ℝ)*(base19) + (716001827/50000000000000 : ℝ)*(base23) + (153047289/100000000000000 : ℝ)*(upper3) + (89820573/50000000000000 : ℝ)*(upper5) + (60820979633081/10000000000000 : ℝ)*(major0) + (60820979633081/10000000000000 : ℝ)*(major1) + (60820979633081/10000000000000 : ℝ)*(major2) + (81786270711369/10000000000000 : ℝ)*(sp0) + (408932878300163/50000000000000 : ℝ)*(sp1) + (163573161565907/20000000000000 : ℝ)*(sp2) + (39855002696671/10000000000000 : ℝ)*(sp3) + (4672275983/100000000000000 : ℝ)*(sp4) + (1994730543/100000000000000 : ℝ)*(sp7) + (398552161253737/100000000000000 : ℝ)*(f.failure) + (204466809958297/25000000000000 : ℝ)*(f.sum) + (8357603338717/2500000000000000000000000000 : ℝ)*base66 + (20857801558717/5000000000000000000000000000 : ℝ)*base68 + (30292747053717/5000000000000000000000000000 : ℝ)*base70 + (9687519018717/5000000000000000000000000000 : ℝ)*base72 + (9110166111217/2500000000000000000000000000 : ℝ)*base74 + (5766130273717/5000000000000000000000000000 : ℝ)*base76 + (30958681758717/5000000000000000000000000000 : ℝ)*base78 + (29674042008717/5000000000000000000000000000 : ℝ)*base80 + (10654940711217/2500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (25451129/10000000000000000000000 : ℝ)*base89 + (25451129/10000000000000000000000 : ℝ)*base91 + (25451129/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (80170785372206819999733/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (204931591/50000000000000 : ℝ)*(base1) + (604104629/50000000000000 : ℝ)*(base19) + (698942789/50000000000000 : ℝ)*(base23) + (235812933/100000000000000 : ℝ)*(upper3) + (641933676696359/100000000000000 : ℝ)*(major0) + (641933676696359/100000000000000 : ℝ)*(major1) + (641933676696359/100000000000000 : ℝ)*(major2) + (955576993/50000000000000 : ℝ)*(sp1) + (392933049/25000000000000 : ℝ)*(sp2) + (2238903/781250000000 : ℝ)*(sp3) + (431608278685707/50000000000000 : ℝ)*(sp4) + (215803257036247/25000000000000 : ℝ)*(sp5) + (431606588945229/50000000000000 : ℝ)*(sp6) + (84130059130591/20000000000000 : ℝ)*(sp7) + (420650992095721/100000000000000 : ℝ)*(f.failure) + (107902018438529/12500000000000 : ℝ)*(f.sum) + (21434779833363/25000000000000000000000000000 : ℝ)*base66 + (188311926208363/50000000000000000000000000000 : ℝ)*base68 + (479377847458363/50000000000000000000000000000 : ℝ)*base70 + (161775718608363/50000000000000000000000000000 : ℝ)*base72 + (15096938083363/25000000000000000000000000000 : ℝ)*base74 + (220310029058363/50000000000000000000000000000 : ℝ)*base76 + (384625782808363/50000000000000000000000000000 : ℝ)*base78 + (50597979208363/50000000000000000000000000000 : ℝ)*base80 + (98610617908363/25000000000000000000000000000 : ℝ)*base82 + (49688057/10000000000000000000000 : ℝ)*base89 + (49688057/10000000000000000000000 : ℝ)*base91 + (49688057/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1288_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152604817/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1001/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5453/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1288_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1288_s1_0 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1017063491/5000000000 : ℝ)*x 0 + (177101171/312500000 : ℝ)*x 1 + (1005575099/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1017063491/5000000000 : ℝ)^531 ≤ (76663138269/625000000000 : ℝ)^403 := by
    have hnat : (1017063491 : ℕ)^531*625000000000^403 ≤ 76663138269^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017063491 5000000000 76663138269 625000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (177101171/312500000 : ℝ)^531 ≤ (47319240461/100000000000 : ℝ)^403 := by
    have hnat : (177101171 : ℕ)^531*100000000000^403 ≤ 47319240461^403*312500000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177101171 312500000 47319240461 100000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1005575099/2000000000 : ℝ)^531 ≤ (40414657397131/100000000000000 : ℝ)^403 := by
    have hnat : (1005575099 : ℕ)^531*100000000000000^403 ≤ 40414657397131^403*2000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005575099 2000000000 40414657397131 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1017063491/5000000000 : ℝ), (177101171/312500000 : ℝ), (1005575099/2000000000 : ℝ)] ![(76663138269/625000000000 : ℝ), (47319240461/100000000000 : ℝ), (40414657397131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1017063491/5000000000 : ℝ)|^531 ≤ (76663138269/625000000000 : ℝ)^403
        have hw : |(-1017063491/5000000000 : ℝ)|=(1017063491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(177101171/312500000 : ℝ)|^531 ≤ (47319240461/100000000000 : ℝ)^403
        have hw : |(177101171/312500000 : ℝ)|=(177101171/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1005575099/2000000000 : ℝ)|^531 ≤ (40414657397131/100000000000000 : ℝ)^403
        have hw : |(1005575099/2000000000 : ℝ)|=(1005575099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s1_1 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1352853119/2500000000 : ℝ)*x 0 + (-297117641/1250000000 : ℝ)*x 1 + (1256968849/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1352853119/2500000000 : ℝ)^531 ≤ (5565643000159/12500000000000 : ℝ)^403 := by
    have hnat : (1352853119 : ℕ)^531*12500000000000^403 ≤ 5565643000159^403*2500000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352853119 2500000000 5565643000159 12500000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (297117641/1250000000 : ℝ)^531 ≤ (3012039928761/20000000000000 : ℝ)^403 := by
    have hnat : (297117641 : ℕ)^531*20000000000000^403 ≤ 3012039928761^403*1250000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297117641 1250000000 3012039928761 20000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1256968849/2500000000 : ℝ)^531 ≤ (20207328174303/50000000000000 : ℝ)^403 := by
    have hnat : (1256968849 : ℕ)^531*50000000000000^403 ≤ 20207328174303^403*2500000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1256968849 2500000000 20207328174303 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1352853119/2500000000 : ℝ), (-297117641/1250000000 : ℝ), (1256968849/2500000000 : ℝ)] ![(5565643000159/12500000000000 : ℝ), (3012039928761/20000000000000 : ℝ), (20207328174303/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1352853119/2500000000 : ℝ)|^531 ≤ (5565643000159/12500000000000 : ℝ)^403
        have hw : |(1352853119/2500000000 : ℝ)|=(1352853119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-297117641/1250000000 : ℝ)|^531 ≤ (3012039928761/20000000000000 : ℝ)^403
        have hw : |(-297117641/1250000000 : ℝ)|=(297117641/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1256968849/2500000000 : ℝ)|^531 ≤ (20207328174303/50000000000000 : ℝ)^403
        have hw : |(1256968849/2500000000 : ℝ)|=(1256968849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s1_2 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2705706141/5000000000 : ℝ)*x 0 + (5027875509/10000000000 : ℝ)*x 1 + (-475388247/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2705706141/5000000000 : ℝ)^531 ≤ (22262570949023/50000000000000 : ℝ)^403 := by
    have hnat : (2705706141 : ℕ)^531*50000000000000^403 ≤ 22262570949023^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705706141 5000000000 22262570949023 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5027875509/10000000000 : ℝ)^531 ≤ (631479024147/1562500000000 : ℝ)^403 := by
    have hnat : (5027875509 : ℕ)^531*1562500000000^403 ≤ 631479024147^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5027875509 10000000000 631479024147 1562500000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (475388247/2000000000 : ℝ)^531 ≤ (15060200537081/100000000000000 : ℝ)^403 := by
    have hnat : (475388247 : ℕ)^531*100000000000000^403 ≤ 15060200537081^403*2000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      475388247 2000000000 15060200537081 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2705706141/5000000000 : ℝ), (5027875509/10000000000 : ℝ), (-475388247/2000000000 : ℝ)] ![(22262570949023/50000000000000 : ℝ), (631479024147/1562500000000 : ℝ), (15060200537081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2705706141/5000000000 : ℝ)|^531 ≤ (22262570949023/50000000000000 : ℝ)^403
        have hw : |(2705706141/5000000000 : ℝ)|=(2705706141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5027875509/10000000000 : ℝ)|^531 ≤ (631479024147/1562500000000 : ℝ)^403
        have hw : |(5027875509/10000000000 : ℝ)|=(5027875509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-475388247/2000000000 : ℝ)|^531 ≤ (15060200537081/100000000000000 : ℝ)^403
        have hw : |(-475388247/2000000000 : ℝ)|=(475388247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s1_3 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4301838989/10000000000 : ℝ)*x 0 + (1846647283/5000000000 : ℝ)*x 1 + (625665827/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4301838989/10000000000 : ℝ)^531 ≤ (32907596593439/100000000000000 : ℝ)^403 := by
    have hnat : (4301838989 : ℕ)^531*100000000000000^403 ≤ 32907596593439^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301838989 10000000000 32907596593439 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1846647283/5000000000 : ℝ)^531 ≤ (26916394694077/100000000000000 : ℝ)^403 := by
    have hnat : (1846647283 : ℕ)^531*100000000000000^403 ≤ 26916394694077^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1846647283 5000000000 26916394694077 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (625665827/1250000000 : ℝ)^531 ≤ (2511000543423/6250000000000 : ℝ)^403 := by
    have hnat : (625665827 : ℕ)^531*6250000000000^403 ≤ 2511000543423^403*1250000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625665827 1250000000 2511000543423 6250000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4301838989/10000000000 : ℝ), (1846647283/5000000000 : ℝ), (625665827/1250000000 : ℝ)] ![(32907596593439/100000000000000 : ℝ), (26916394694077/100000000000000 : ℝ), (2511000543423/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4301838989/10000000000 : ℝ)|^531 ≤ (32907596593439/100000000000000 : ℝ)^403
        have hw : |(4301838989/10000000000 : ℝ)|=(4301838989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1846647283/5000000000 : ℝ)|^531 ≤ (26916394694077/100000000000000 : ℝ)^403
        have hw : |(1846647283/5000000000 : ℝ)|=(1846647283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(625665827/1250000000 : ℝ)|^531 ≤ (2511000543423/6250000000000 : ℝ)^403
        have hw : |(625665827/1250000000 : ℝ)|=(625665827/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s1_4 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1017386407/5000000000 : ℝ)*x 0 + (314764801/625000000 : ℝ)*x 1 + (2829358737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1017386407/5000000000 : ℝ)^531 ≤ (12271233801611/100000000000000 : ℝ)^403 := by
    have hnat : (1017386407 : ℕ)^531*100000000000000^403 ≤ 12271233801611^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017386407 5000000000 12271233801611 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (314764801/625000000 : ℝ)^531 ≤ (4050323693219/10000000000000 : ℝ)^403 := by
    have hnat : (314764801 : ℕ)^531*10000000000000^403 ≤ 4050323693219^403*625000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314764801 625000000 4050323693219 10000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2829358737/5000000000 : ℝ)^531 ≤ (47225529242253/100000000000000 : ℝ)^403 := by
    have hnat : (2829358737 : ℕ)^531*100000000000000^403 ≤ 47225529242253^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2829358737 5000000000 47225529242253 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1017386407/5000000000 : ℝ), (314764801/625000000 : ℝ), (2829358737/5000000000 : ℝ)] ![(12271233801611/100000000000000 : ℝ), (4050323693219/10000000000000 : ℝ), (47225529242253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1017386407/5000000000 : ℝ)|^531 ≤ (12271233801611/100000000000000 : ℝ)^403
        have hw : |(-1017386407/5000000000 : ℝ)|=(1017386407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(314764801/625000000 : ℝ)|^531 ≤ (4050323693219/10000000000000 : ℝ)^403
        have hw : |(314764801/625000000 : ℝ)|=(314764801/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2829358737/5000000000 : ℝ)|^531 ≤ (47225529242253/100000000000000 : ℝ)^403
        have hw : |(2829358737/5000000000 : ℝ)|=(2829358737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s1_5 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5246282609/10000000000 : ℝ)*x 0 + (-174609883/1000000000 : ℝ)*x 1 + (5658718059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5246282609/10000000000 : ℝ)^531 ≤ (42743646611503/100000000000000 : ℝ)^403 := by
    have hnat : (5246282609 : ℕ)^531*100000000000000^403 ≤ 42743646611503^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246282609 10000000000 42743646611503 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (174609883/1000000000 : ℝ)^531 ≤ (10030817703877/100000000000000 : ℝ)^403 := by
    have hnat : (174609883 : ℕ)^531*100000000000000^403 ≤ 10030817703877^403*1000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174609883 1000000000 10030817703877 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5658718059/10000000000 : ℝ)^531 ≤ (23612767837557/50000000000000 : ℝ)^403 := by
    have hnat : (5658718059 : ℕ)^531*50000000000000^403 ≤ 23612767837557^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5658718059 10000000000 23612767837557 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5246282609/10000000000 : ℝ), (-174609883/1000000000 : ℝ), (5658718059/10000000000 : ℝ)] ![(42743646611503/100000000000000 : ℝ), (10030817703877/100000000000000 : ℝ), (23612767837557/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5246282609/10000000000 : ℝ)|^531 ≤ (42743646611503/100000000000000 : ℝ)^403
        have hw : |(5246282609/10000000000 : ℝ)|=(5246282609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-174609883/1000000000 : ℝ)|^531 ≤ (10030817703877/100000000000000 : ℝ)^403
        have hw : |(-174609883/1000000000 : ℝ)|=(174609883/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5658718059/10000000000 : ℝ)|^531 ≤ (23612767837557/50000000000000 : ℝ)^403
        have hw : |(5658718059/10000000000 : ℝ)|=(5658718059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s1_6 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1311570629/2500000000 : ℝ)*x 0 + (565871769/1000000000 : ℝ)*x 1 + (-1746099497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1311570629/2500000000 : ℝ)^531 ≤ (42743645613131/100000000000000 : ℝ)^403 := by
    have hnat : (1311570629 : ℕ)^531*100000000000000^403 ≤ 42743645613131^403*2500000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311570629 2500000000 42743645613131 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (565871769/1000000000 : ℝ)^531 ≤ (47225531617463/100000000000000 : ℝ)^403 := by
    have hnat : (565871769 : ℕ)^531*100000000000000^403 ≤ 47225531617463^403*1000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565871769 1000000000 47225531617463 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1746099497/10000000000 : ℝ)^531 ≤ (2006164550523/20000000000000 : ℝ)^403 := by
    have hnat : (1746099497 : ℕ)^531*20000000000000^403 ≤ 2006164550523^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1746099497 10000000000 2006164550523 20000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1311570629/2500000000 : ℝ), (565871769/1000000000 : ℝ), (-1746099497/10000000000 : ℝ)] ![(42743645613131/100000000000000 : ℝ), (47225531617463/100000000000000 : ℝ), (2006164550523/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1311570629/2500000000 : ℝ)|^531 ≤ (42743645613131/100000000000000 : ℝ)^403
        have hw : |(1311570629/2500000000 : ℝ)|=(1311570629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(565871769/1000000000 : ℝ)|^531 ≤ (47225531617463/100000000000000 : ℝ)^403
        have hw : |(565871769/1000000000 : ℝ)|=(565871769/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1746099497/10000000000 : ℝ)|^531 ≤ (2006164550523/20000000000000 : ℝ)^403
        have hw : |(-1746099497/10000000000 : ℝ)|=(1746099497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s1_7 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (860632733/2000000000 : ℝ)*x 0 + (623521091/1250000000 : ℝ)*x 1 + (3710777749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (860632733/2000000000 : ℝ)^531 ≤ (6584189817493/20000000000000 : ℝ)^403 := by
    have hnat : (860632733 : ℕ)^531*20000000000000^403 ≤ 6584189817493^403*2000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860632733 2000000000 6584189817493 20000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (623521091/1250000000 : ℝ)^531 ≤ (39994644731259/100000000000000 : ℝ)^403 := by
    have hnat : (623521091 : ℕ)^531*100000000000000^403 ≤ 39994644731259^403*1250000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623521091 1250000000 39994644731259 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3710777749/10000000000 : ℝ)^531 ≤ (27084406164623/100000000000000 : ℝ)^403 := by
    have hnat : (3710777749 : ℕ)^531*100000000000000^403 ≤ 27084406164623^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3710777749 10000000000 27084406164623 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(860632733/2000000000 : ℝ), (623521091/1250000000 : ℝ), (3710777749/10000000000 : ℝ)] ![(6584189817493/20000000000000 : ℝ), (39994644731259/100000000000000 : ℝ), (27084406164623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(860632733/2000000000 : ℝ)|^531 ≤ (6584189817493/20000000000000 : ℝ)^403
        have hw : |(860632733/2000000000 : ℝ)|=(860632733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(623521091/1250000000 : ℝ)|^531 ≤ (39994644731259/100000000000000 : ℝ)^403
        have hw : |(623521091/1250000000 : ℝ)|=(623521091/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3710777749/10000000000 : ℝ)|^531 ≤ (27084406164623/100000000000000 : ℝ)^403
        have hw : |(3710777749/10000000000 : ℝ)|=(3710777749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1288_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152604817/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5453/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1001/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (6369/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19883/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5453/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1001/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5453/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1001/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5453/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1001/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5453/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1001/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5453/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1001/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5453/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1001/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1001/100000 : ℝ) ^ (4247/1024 : ℝ) ≤ (5091883333/1000000000000000000 : ℝ) := by
    have hpowers : (1001/100000 : ℝ)^4247 ≤ (5091883333/1000000000000000000 : ℝ)^1024 := by
      have hnat : (1001 : ℕ)^4247*1000000000000000000^1024 ≤ 5091883333^1024*100000^4247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1001 100000 5091883333 1000000000000000000 4247 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1001/100000 : ℝ)) (X := (5091883333/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (5453/20000 : ℝ) ^ (4247/1024 : ℝ) ≤ (114060658612290577/25000000000000000000 : ℝ) := by
    have hpowers : (5453/20000 : ℝ)^4247 ≤ (114060658612290577/25000000000000000000 : ℝ)^1024 := by
      have hnat : (5453 : ℕ)^4247*25000000000000000000^1024 ≤ 114060658612290577^1024*20000^4247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5453 20000 114060658612290577 25000000000000000000 4247 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5453/20000 : ℝ)) (X := (114060658612290577/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (500000005091883333/500000000000000000 : ℝ) ≤ (500000001227711/500000000000000 : ℝ) ^ (4247/1024 : ℝ) := by
    have hpowers : (500000005091883333/500000000000000000 : ℝ)^1024 ≤ (500000001227711/500000000000000 : ℝ)^4247 := by
      have hnat : (500000005091883333 : ℕ)^1024*500000000000000^4247 ≤ 500000001227711^4247*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500000005091883333 500000000000000000 500000001227711 500000000000000 1024 4247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500000001227711/500000000000000 : ℝ)) (X := (500000005091883333/500000000000000000 : ℝ)) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12557030392954686951/12500000000000000000 : ℝ) ≤ (10010981547836039/10000000000000000 : ℝ) ^ (4247/1024 : ℝ) := by
    have hpowers : (12557030392954686951/12500000000000000000 : ℝ)^1024 ≤ (10010981547836039/10000000000000000 : ℝ)^4247 := by
      have hnat : (12557030392954686951 : ℕ)^1024*10000000000000000^4247 ≤ 10010981547836039^4247*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12557030392954686951 12500000000000000000 10010981547836039 10000000000000000 1024 4247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10010981547836039/10000000000000000 : ℝ)) (X := (12557030392954686951/12500000000000000000 : ℝ)) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12614060658612290577/12500000000000000000 : ℝ) ≤ (5010981535558929/5000000000000000 : ℝ) ^ (4247/1024 : ℝ) := by
    have hpowers : (12614060658612290577/12500000000000000000 : ℝ)^1024 ≤ (5010981535558929/5000000000000000 : ℝ)^4247 := by
      have hnat : (12614060658612290577 : ℕ)^1024*5000000000000000^4247 ≤ 5010981535558929^4247*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12614060658612290577 12500000000000000000 5010981535558929 5000000000000000 1024 4247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5010981535558929/5000000000000000 : ℝ)) (X := (12614060658612290577/12500000000000000000 : ℝ)) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5091883333/1000000000000000000 : ℝ) ≤ ((18758429688234416603/18760000000000000000 : ℝ)+2*(10981523281819/2626400000000000 : ℝ)*(1001/100000 : ℝ))^(4247/1024 : ℝ) := by
    rw [show (18758429688234416603/18760000000000000000 : ℝ)+2*(10981523281819/2626400000000000 : ℝ)*(1001/100000 : ℝ)=(500000001227711/500000000000000 : ℝ) by norm_num, show 1+2*(5091883333/1000000000000000000 : ℝ)=(500000005091883333/500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(114060658612290577/25000000000000000000 : ℝ)+(5091883333/1000000000000000000 : ℝ) ≤ ((18758429688234416603/18760000000000000000 : ℝ)+(10981523281819/2626400000000000 : ℝ)*((5453/20000 : ℝ)+(1001/100000 : ℝ)))^(4247/1024 : ℝ) := by
    rw [show (18758429688234416603/18760000000000000000 : ℝ)+(10981523281819/2626400000000000 : ℝ)*((5453/20000 : ℝ)+(1001/100000 : ℝ))=(10010981547836039/10000000000000000 : ℝ) by norm_num, show 1+(114060658612290577/25000000000000000000 : ℝ)+(5091883333/1000000000000000000 : ℝ)=(12557030392954686951/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(114060658612290577/25000000000000000000 : ℝ) ≤ ((18758429688234416603/18760000000000000000 : ℝ)+2*(10981523281819/2626400000000000 : ℝ)*(5453/20000 : ℝ))^(4247/1024 : ℝ) := by
    rw [show (18758429688234416603/18760000000000000000 : ℝ)+2*(10981523281819/2626400000000000 : ℝ)*(5453/20000 : ℝ)=(5010981535558929/5000000000000000 : ℝ) by norm_num, show 1+2*(114060658612290577/25000000000000000000 : ℝ)=(12614060658612290577/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18758429688234416603/18760000000000000000 : ℝ)*(X 1 0+X 2 0)+(10981523281819/2626400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4247/1024 : ℝ)) (lo := (1001/100000 : ℝ)) (hi := (5453/20000 : ℝ)) (c := (18758429688234416603/18760000000000000000 : ℝ)) (alpha := (10981523281819/2626400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18758429688234416603/18760000000000000000 : ℝ)*(X 0 1+X 2 1)+(10981523281819/2626400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4247/1024 : ℝ)) (lo := (1001/100000 : ℝ)) (hi := (5453/20000 : ℝ)) (c := (18758429688234416603/18760000000000000000 : ℝ)) (alpha := (10981523281819/2626400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18758429688234416603/18760000000000000000 : ℝ)*(X 0 2+X 1 2)+(10981523281819/2626400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4247/1024 : ℝ)) (lo := (1001/100000 : ℝ)) (hi := (5453/20000 : ℝ)) (c := (18758429688234416603/18760000000000000000 : ℝ)) (alpha := (10981523281819/2626400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1017063491/5000000000 : ℝ)*X 0 0+(177101171/312500000 : ℝ)*X 0 1+(1005575099/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1352853119/2500000000 : ℝ)*X 1 0+(-297117641/1250000000 : ℝ)*X 1 1+(1256968849/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2705706141/5000000000 : ℝ)*X 2 0+(5027875509/10000000000 : ℝ)*X 2 1+(-475388247/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4301838989/10000000000 : ℝ)*X 0 0+(1846647283/5000000000 : ℝ)*X 0 1+(625665827/1250000000 : ℝ)*X 0 2+(4301838989/10000000000 : ℝ)*X 1 0+(1846647283/5000000000 : ℝ)*X 1 1+(625665827/1250000000 : ℝ)*X 1 2+(4301838989/10000000000 : ℝ)*X 2 0+(1846647283/5000000000 : ℝ)*X 2 1+(625665827/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1017386407/5000000000 : ℝ)*X 0 0+(314764801/625000000 : ℝ)*X 0 1+(2829358737/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5246282609/10000000000 : ℝ)*X 1 0+(-174609883/1000000000 : ℝ)*X 1 1+(5658718059/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1311570629/2500000000 : ℝ)*X 2 0+(565871769/1000000000 : ℝ)*X 2 1+(-1746099497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((860632733/2000000000 : ℝ)*X 0 0+(623521091/1250000000 : ℝ)*X 0 1+(3710777749/10000000000 : ℝ)*X 0 2+(860632733/2000000000 : ℝ)*X 1 0+(623521091/1250000000 : ℝ)*X 1 1+(3710777749/10000000000 : ℝ)*X 1 2+(860632733/2000000000 : ℝ)*X 2 0+(623521091/1250000000 : ℝ)*X 2 1+(3710777749/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36534905237102473419611469/14656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11804301/50000000000000 : ℝ)*(base1) + (95056419/20000000000000 : ℝ)*(base19) + (5240127/1250000000000 : ℝ)*(base23) + (72720681/100000000000000 : ℝ)*(upper3) + (867821/5000000000000 : ℝ)*(upper5) + (18173773607259/1562500000000 : ℝ)*(major0) + (18173773607259/1562500000000 : ℝ)*(major1) + (18173773607259/1562500000000 : ℝ)*(major2) + (78203101835299/5000000000000 : ℝ)*(sp0) + (1564063697486911/100000000000000 : ℝ)*(sp1) + (782031876779423/50000000000000 : ℝ)*(sp2) + (381088755030661/50000000000000 : ℝ)*(sp3) + (539917907/25000000000000 : ℝ)*(sp4) + (1232197327/100000000000000 : ℝ)*(sp7) + (3048715063469/400000000000 : ℝ)*(f.failure) + (782032086384503/50000000000000 : ℝ)*(f.sum) + (5045129127847/16415000000000000000000000000 : ℝ)*base66 + (448239204905748239/205187500000000000000000000000000 : ℝ)*base67 + (333321158523814261/205187500000000000000000000000000 : ℝ)*base70 + (375827872784560739/205187500000000000000000000000000 : ℝ)*base71 + (3410191413117/4103750000000000000000000000 : ℝ)*base73 + (337702729115814261/205187500000000000000000000000000 : ℝ)*base76 + (289229527479060739/205187500000000000000000000000000 : ℝ)*base77 + (307282859999623239/205187500000000000000000000000000 : ℝ)*base79 + (19399637960007/16415000000000000000000000000 : ℝ)*base82 + (269827/40000000000000000000 : ℝ)*base90 + (269827/40000000000000000000 : ℝ)*base92 + (269827/40000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (581244317438877602956574997/58625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12333449/50000000000000 : ℝ)*(base1) + (956767157/50000000000000 : ℝ)*(base19) + (921436483/50000000000000 : ℝ)*(base23) + (33961303/12500000000000 : ℝ)*(upper3) + (216210507/100000000000000 : ℝ)*(upper5) + (149332561110733/12500000000000 : ℝ)*(major0) + (149332561110733/12500000000000 : ℝ)*(major1) + (149332561110733/12500000000000 : ℝ)*(major2) + (10130089231/100000000000000 : ℝ)*(sp1) + (8789892423/100000000000000 : ℝ)*(sp2) + (401618703505409/25000000000000 : ℝ)*(sp4) + (1606462745731193/100000000000000 : ℝ)*(sp5) + (401616039147337/25000000000000 : ℝ)*(sp6) + (782845833262911/100000000000000 : ℝ)*(sp7) + (48927866120613/6250000000000 : ℝ)*(f.failure) + (803237394677369/50000000000000 : ℝ)*(f.sum) + (1043519145267/1172500000000000000000000000 : ℝ)*base66 + (755310697473250001/234500000000000000000000000000000 : ℝ)*base68 + (440456134628750001/234500000000000000000000000000000 : ℝ)*base70 + (1083258742051250001/234500000000000000000000000000000 : ℝ)*base72 + (6120732210489/2345000000000000000000000000 : ℝ)*base74 + (199133919694250001/234500000000000000000000000000000 : ℝ)*base76 + (1888487271705750001/234500000000000000000000000000000 : ℝ)*base78 + (2130028083267249999/234500000000000000000000000000000 : ℝ)*base79 + (5140434931351/2345000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (3207179/625000000000000000000 : ℝ)*base90 + (3207179/625000000000000000000 : ℝ)*base92 + (3207179/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1288_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152604817/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5453/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1001/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6369/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19883/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1288_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1288_s2_0 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1039599707/5000000000 : ℝ)*x 0 + (1099098883/2000000000 : ℝ)*x 1 + (5170836497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039599707/5000000000 : ℝ)^531 ≤ (315636908947/2500000000000 : ℝ)^403 := by
    have hnat : (1039599707 : ℕ)^531*2500000000000^403 ≤ 315636908947^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039599707 5000000000 315636908947 2500000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1099098883/2000000000 : ℝ)^531 ≤ (45438948853209/100000000000000 : ℝ)^403 := by
    have hnat : (1099098883 : ℕ)^531*100000000000000^403 ≤ 45438948853209^403*2000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099098883 2000000000 45438948853209 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5170836497/10000000000 : ℝ)^531 ≤ (41935574766063/100000000000000 : ℝ)^403 := by
    have hnat : (5170836497 : ℕ)^531*100000000000000^403 ≤ 41935574766063^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170836497 10000000000 41935574766063 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1039599707/5000000000 : ℝ), (1099098883/2000000000 : ℝ), (5170836497/10000000000 : ℝ)] ![(315636908947/2500000000000 : ℝ), (45438948853209/100000000000000 : ℝ), (41935574766063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1039599707/5000000000 : ℝ)|^531 ≤ (315636908947/2500000000000 : ℝ)^403
        have hw : |(-1039599707/5000000000 : ℝ)|=(1039599707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1099098883/2000000000 : ℝ)|^531 ≤ (45438948853209/100000000000000 : ℝ)^403
        have hw : |(1099098883/2000000000 : ℝ)|=(1099098883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5170836497/10000000000 : ℝ)|^531 ≤ (41935574766063/100000000000000 : ℝ)^403
        have hw : |(5170836497/10000000000 : ℝ)|=(5170836497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s2_1 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2684943381/5000000000 : ℝ)*x 0 + (-56187141/250000000 : ℝ)*x 1 + (8273339/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684943381/5000000000 : ℝ)^531 ≤ (44075497963291/100000000000000 : ℝ)^403 := by
    have hnat : (2684943381 : ℕ)^531*100000000000000^403 ≤ 44075497963291^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684943381 5000000000 44075497963291 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56187141/250000000 : ℝ)^531 ≤ (6994461610293/50000000000000 : ℝ)^403 := by
    have hnat : (56187141 : ℕ)^531*50000000000000^403 ≤ 6994461610293^403*250000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56187141 250000000 6994461610293 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8273339/16000000 : ℝ)^531 ≤ (8387115761067/20000000000000 : ℝ)^403 := by
    have hnat : (8273339 : ℕ)^531*20000000000000^403 ≤ 8387115761067^403*16000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8273339 16000000 8387115761067 20000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684943381/5000000000 : ℝ), (-56187141/250000000 : ℝ), (8273339/16000000 : ℝ)] ![(44075497963291/100000000000000 : ℝ), (6994461610293/50000000000000 : ℝ), (8387115761067/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684943381/5000000000 : ℝ)|^531 ≤ (44075497963291/100000000000000 : ℝ)^403
        have hw : |(2684943381/5000000000 : ℝ)|=(2684943381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-56187141/250000000 : ℝ)|^531 ≤ (6994461610293/50000000000000 : ℝ)^403
        have hw : |(-56187141/250000000 : ℝ)|=(56187141/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8273339/16000000 : ℝ)|^531 ≤ (8387115761067/20000000000000 : ℝ)^403
        have hw : |(8273339/16000000 : ℝ)|=(8273339/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s2_2 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5369886959/10000000000 : ℝ)*x 0 + (323177283/625000000 : ℝ)*x 1 + (-2247485833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369886959/10000000000 : ℝ)^531 ≤ (22037750046911/50000000000000 : ℝ)^403 := by
    have hnat : (5369886959 : ℕ)^531*50000000000000^403 ≤ 22037750046911^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369886959 10000000000 22037750046911 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (323177283/625000000 : ℝ)^531 ≤ (20967787548663/50000000000000 : ℝ)^403 := by
    have hnat : (323177283 : ℕ)^531*50000000000000^403 ≤ 20967787548663^403*625000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323177283 625000000 20967787548663 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2247485833/10000000000 : ℝ)^531 ≤ (2797784960683/20000000000000 : ℝ)^403 := by
    have hnat : (2247485833 : ℕ)^531*20000000000000^403 ≤ 2797784960683^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247485833 10000000000 2797784960683 20000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369886959/10000000000 : ℝ), (323177283/625000000 : ℝ), (-2247485833/10000000000 : ℝ)] ![(22037750046911/50000000000000 : ℝ), (20967787548663/50000000000000 : ℝ), (2797784960683/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369886959/10000000000 : ℝ)|^531 ≤ (22037750046911/50000000000000 : ℝ)^403
        have hw : |(5369886959/10000000000 : ℝ)|=(5369886959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(323177283/625000000 : ℝ)|^531 ≤ (20967787548663/50000000000000 : ℝ)^403
        have hw : |(323177283/625000000 : ℝ)|=(323177283/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2247485833/10000000000 : ℝ)|^531 ≤ (2797784960683/20000000000000 : ℝ)^403
        have hw : |(-2247485833/10000000000 : ℝ)|=(2247485833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s2_3 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2166578339/5000000000 : ℝ)*x 0 + (200613061/500000000 : ℝ)*x 1 + (4678497549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166578339/5000000000 : ℝ)^531 ≤ (4152952766729/12500000000000 : ℝ)^403 := by
    have hnat : (2166578339 : ℕ)^531*12500000000000^403 ≤ 4152952766729^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166578339 5000000000 4152952766729 12500000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200613061/500000000 : ℝ)^531 ≤ (7505135421691/25000000000000 : ℝ)^403 := by
    have hnat : (200613061 : ℕ)^531*25000000000000^403 ≤ 7505135421691^403*500000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200613061 500000000 7505135421691 25000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4678497549/10000000000 : ℝ)^531 ≤ (36755836165849/100000000000000 : ℝ)^403 := by
    have hnat : (4678497549 : ℕ)^531*100000000000000^403 ≤ 36755836165849^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4678497549 10000000000 36755836165849 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2166578339/5000000000 : ℝ), (200613061/500000000 : ℝ), (4678497549/10000000000 : ℝ)] ![(4152952766729/12500000000000 : ℝ), (7505135421691/25000000000000 : ℝ), (36755836165849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2166578339/5000000000 : ℝ)|^531 ≤ (4152952766729/12500000000000 : ℝ)^403
        have hw : |(2166578339/5000000000 : ℝ)|=(2166578339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(200613061/500000000 : ℝ)|^531 ≤ (7505135421691/25000000000000 : ℝ)^403
        have hw : |(200613061/500000000 : ℝ)|=(200613061/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4678497549/10000000000 : ℝ)|^531 ≤ (36755836165849/100000000000000 : ℝ)^403
        have hw : |(4678497549/10000000000 : ℝ)|=(4678497549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s2_4 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-259910393/1250000000 : ℝ)*x 0 + (323312621/625000000 : ℝ)*x 1 + (2746654343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259910393/1250000000 : ℝ)^531 ≤ (12626146281009/100000000000000 : ℝ)^403 := by
    have hnat : (259910393 : ℕ)^531*100000000000000^403 ≤ 12626146281009^403*1250000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259910393 1250000000 12626146281009 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (323312621/625000000 : ℝ)^531 ≤ (20979357989083/50000000000000 : ℝ)^403 := by
    have hnat : (323312621 : ℕ)^531*50000000000000^403 ≤ 20979357989083^403*625000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323312621 625000000 20979357989083 50000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2746654343/5000000000 : ℝ)^531 ≤ (45415137731221/100000000000000 : ℝ)^403 := by
    have hnat : (2746654343 : ℕ)^531*100000000000000^403 ≤ 45415137731221^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746654343 5000000000 45415137731221 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-259910393/1250000000 : ℝ), (323312621/625000000 : ℝ), (2746654343/5000000000 : ℝ)] ![(12626146281009/100000000000000 : ℝ), (20979357989083/50000000000000 : ℝ), (45415137731221/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-259910393/1250000000 : ℝ)|^531 ≤ (12626146281009/100000000000000 : ℝ)^403
        have hw : |(-259910393/1250000000 : ℝ)|=(259910393/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(323312621/625000000 : ℝ)|^531 ≤ (20979357989083/50000000000000 : ℝ)^403
        have hw : |(323312621/625000000 : ℝ)|=(323312621/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2746654343/5000000000 : ℝ)|^531 ≤ (45415137731221/100000000000000 : ℝ)^403
        have hw : |(2746654343/5000000000 : ℝ)|=(2746654343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s2_5 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1057343227/2000000000 : ℝ)*x 0 + (-30078331/156250000 : ℝ)*x 1 + (5493308831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057343227/2000000000 : ℝ)^531 ≤ (43178238166579/100000000000000 : ℝ)^403 := by
    have hnat : (1057343227 : ℕ)^531*100000000000000^403 ≤ 43178238166579^403*2000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057343227 2000000000 43178238166579 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30078331/156250000 : ℝ)^531 ≤ (1140662252047/10000000000000 : ℝ)^403 := by
    have hnat : (30078331 : ℕ)^531*10000000000000^403 ≤ 1140662252047^403*156250000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30078331 156250000 1140662252047 10000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5493308831/10000000000 : ℝ)^531 ≤ (45415139310737/100000000000000 : ℝ)^403 := by
    have hnat : (5493308831 : ℕ)^531*100000000000000^403 ≤ 45415139310737^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5493308831 10000000000 45415139310737 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057343227/2000000000 : ℝ), (-30078331/156250000 : ℝ), (5493308831/10000000000 : ℝ)] ![(43178238166579/100000000000000 : ℝ), (1140662252047/10000000000000 : ℝ), (45415139310737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057343227/2000000000 : ℝ)|^531 ≤ (43178238166579/100000000000000 : ℝ)^403
        have hw : |(1057343227/2000000000 : ℝ)|=(1057343227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-30078331/156250000 : ℝ)|^531 ≤ (1140662252047/10000000000000 : ℝ)^403
        have hw : |(-30078331/156250000 : ℝ)|=(30078331/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5493308831/10000000000 : ℝ)|^531 ≤ (45415139310737/100000000000000 : ℝ)^403
        have hw : |(5493308831/10000000000 : ℝ)|=(5493308831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s2_6 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1321679077/2500000000 : ℝ)*x 0 + (2746654347/5000000000 : ℝ)*x 1 + (-120313321/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321679077/2500000000 : ℝ)^531 ≤ (43178240028299/100000000000000 : ℝ)^403 := by
    have hnat : (1321679077 : ℕ)^531*100000000000000^403 ≤ 43178240028299^403*2500000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321679077 2500000000 43178240028299 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2746654347/5000000000 : ℝ)^531 ≤ (45415137818367/100000000000000 : ℝ)^403 := by
    have hnat : (2746654347 : ℕ)^531*100000000000000^403 ≤ 45415137818367^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746654347 5000000000 45415137818367 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (120313321/625000000 : ℝ)^531 ≤ (1140662214571/10000000000000 : ℝ)^403 := by
    have hnat : (120313321 : ℕ)^531*10000000000000^403 ≤ 1140662214571^403*625000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120313321 625000000 1140662214571 10000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321679077/2500000000 : ℝ), (2746654347/5000000000 : ℝ), (-120313321/625000000 : ℝ)] ![(43178240028299/100000000000000 : ℝ), (45415137818367/100000000000000 : ℝ), (1140662214571/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321679077/2500000000 : ℝ)|^531 ≤ (43178240028299/100000000000000 : ℝ)^403
        have hw : |(1321679077/2500000000 : ℝ)|=(1321679077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2746654347/5000000000 : ℝ)|^531 ≤ (45415137818367/100000000000000 : ℝ)^403
        have hw : |(2746654347/5000000000 : ℝ)|=(2746654347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-120313321/625000000 : ℝ)|^531 ≤ (1140662214571/10000000000000 : ℝ)^403
        have hw : |(-120313321/625000000 : ℝ)|=(120313321/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1288_s2_7 (p : ℝ) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4333328349/10000000000 : ℝ)*x 0 + (4674052423/10000000000 : ℝ)*x 1 + (2008375597/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4333328349/10000000000 : ℝ)^531 ≤ (519146194747/1562500000000 : ℝ)^403 := by
    have hnat : (4333328349 : ℕ)^531*1562500000000^403 ≤ 519146194747^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4333328349 10000000000 519146194747 1562500000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4674052423/10000000000 : ℝ)^531 ≤ (36709828743381/100000000000000 : ℝ)^403 := by
    have hnat : (4674052423 : ℕ)^531*100000000000000^403 ≤ 36709828743381^403*10000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4674052423 10000000000 36709828743381 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2008375597/5000000000 : ℝ)^531 ≤ (30064814771271/100000000000000 : ℝ)^403 := by
    have hnat : (2008375597 : ℕ)^531*100000000000000^403 ≤ 30064814771271^403*5000000000^531 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008375597 5000000000 30064814771271 100000000000000 531 403 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (531/128 : ℝ)) 531 403 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4333328349/10000000000 : ℝ), (4674052423/10000000000 : ℝ), (2008375597/5000000000 : ℝ)] ![(519146194747/1562500000000 : ℝ), (36709828743381/100000000000000 : ℝ), (30064814771271/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4333328349/10000000000 : ℝ)|^531 ≤ (519146194747/1562500000000 : ℝ)^403
        have hw : |(4333328349/10000000000 : ℝ)|=(4333328349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4674052423/10000000000 : ℝ)|^531 ≤ (36709828743381/100000000000000 : ℝ)^403
        have hw : |(4674052423/10000000000 : ℝ)|=(4674052423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2008375597/5000000000 : ℝ)|^531 ≤ (30064814771271/100000000000000 : ℝ)^403
        have hw : |(2008375597/5000000000 : ℝ)|=(2008375597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1288_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152604817/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19883/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6369/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (379/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1021/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19883/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6369/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19883/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6369/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19883/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6369/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19883/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6369/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19883/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6369/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19883/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6369/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6369/100000 : ℝ) ^ (4247/1024 : ℝ) ≤ (548153542409959/50000000000000000000 : ℝ) := by
    have hpowers : (6369/100000 : ℝ)^4247 ≤ (548153542409959/50000000000000000000 : ℝ)^1024 := by
      have hnat : (6369 : ℕ)^4247*50000000000000000000^1024 ≤ 548153542409959^1024*100000^4247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6369 100000 548153542409959 50000000000000000000 4247 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6369/100000 : ℝ)) (X := (548153542409959/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19883/100000 : ℝ) ^ (4247/1024 : ℝ) ≤ (30790812128994367/25000000000000000000 : ℝ) := by
    have hpowers : (19883/100000 : ℝ)^4247 ≤ (30790812128994367/25000000000000000000 : ℝ)^1024 := by
      have hnat : (19883 : ℕ)^4247*25000000000000000000^1024 ≤ 30790812128994367^1024*100000^4247 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19883 100000 30790812128994367 25000000000000000000 4247 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19883/100000 : ℝ)) (X := (30790812128994367/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000548153542409959/25000000000000000000 : ℝ) ≤ (5000026432990701/5000000000000000 : ℝ) ^ (4247/1024 : ℝ) := by
    have hpowers : (25000548153542409959/25000000000000000000 : ℝ)^1024 ≤ (5000026432990701/5000000000000000 : ℝ)^4247 := by
      have hnat : (25000548153542409959 : ℕ)^1024*5000000000000000^4247 ≤ 5000026432990701^4247*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000548153542409959 25000000000000000000 5000026432990701 5000000000000000 1024 4247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000026432990701/5000000000000000 : ℝ)) (X := (25000548153542409959/25000000000000000000 : ℝ)) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50062129777800398693/50000000000000000000 : ℝ) ≤ (5001497313805459/5000000000000000 : ℝ) ^ (4247/1024 : ℝ) := by
    have hpowers : (50062129777800398693/50000000000000000000 : ℝ)^1024 ≤ (5001497313805459/5000000000000000 : ℝ)^4247 := by
      have hnat : (50062129777800398693 : ℕ)^1024*5000000000000000^4247 ≤ 5001497313805459^4247*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50062129777800398693 50000000000000000000 5001497313805459 5000000000000000 1024 4247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001497313805459/5000000000000000 : ℝ)) (X := (50062129777800398693/50000000000000000000 : ℝ)) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12530790812128994367/12500000000000000000 : ℝ) ≤ (5002968194620217/5000000000000000 : ℝ) ^ (4247/1024 : ℝ) := by
    have hpowers : (12530790812128994367/12500000000000000000 : ℝ)^1024 ≤ (5002968194620217/5000000000000000 : ℝ)^4247 := by
      have hnat : (12530790812128994367 : ℕ)^1024*5000000000000000^4247 ≤ 5002968194620217^4247*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12530790812128994367 12500000000000000000 5002968194620217 5000000000000000 1024 4247 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002968194620217/5000000000000000 : ℝ)) (X := (12530790812128994367/12500000000000000000 : ℝ)) (by norm_num) 4247 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(548153542409959/50000000000000000000 : ℝ) ≤ ((6755162113561794591/6757000000000000000 : ℝ)+2*(735440407379/337850000000000 : ℝ)*(6369/100000 : ℝ))^(4247/1024 : ℝ) := by
    rw [show (6755162113561794591/6757000000000000000 : ℝ)+2*(735440407379/337850000000000 : ℝ)*(6369/100000 : ℝ)=(5000026432990701/5000000000000000 : ℝ) by norm_num, show 1+2*(548153542409959/50000000000000000000 : ℝ)=(25000548153542409959/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30790812128994367/25000000000000000000 : ℝ)+(548153542409959/50000000000000000000 : ℝ) ≤ ((6755162113561794591/6757000000000000000 : ℝ)+(735440407379/337850000000000 : ℝ)*((19883/100000 : ℝ)+(6369/100000 : ℝ)))^(4247/1024 : ℝ) := by
    rw [show (6755162113561794591/6757000000000000000 : ℝ)+(735440407379/337850000000000 : ℝ)*((19883/100000 : ℝ)+(6369/100000 : ℝ))=(5001497313805459/5000000000000000 : ℝ) by norm_num, show 1+(30790812128994367/25000000000000000000 : ℝ)+(548153542409959/50000000000000000000 : ℝ)=(50062129777800398693/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30790812128994367/25000000000000000000 : ℝ) ≤ ((6755162113561794591/6757000000000000000 : ℝ)+2*(735440407379/337850000000000 : ℝ)*(19883/100000 : ℝ))^(4247/1024 : ℝ) := by
    rw [show (6755162113561794591/6757000000000000000 : ℝ)+2*(735440407379/337850000000000 : ℝ)*(19883/100000 : ℝ)=(5002968194620217/5000000000000000 : ℝ) by norm_num, show 1+2*(30790812128994367/25000000000000000000 : ℝ)=(12530790812128994367/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6755162113561794591/6757000000000000000 : ℝ)*(X 1 0+X 2 0)+(735440407379/337850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4247/1024 : ℝ)) (lo := (6369/100000 : ℝ)) (hi := (19883/100000 : ℝ)) (c := (6755162113561794591/6757000000000000000 : ℝ)) (alpha := (735440407379/337850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6755162113561794591/6757000000000000000 : ℝ)*(X 0 1+X 2 1)+(735440407379/337850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4247/1024 : ℝ)) (lo := (6369/100000 : ℝ)) (hi := (19883/100000 : ℝ)) (c := (6755162113561794591/6757000000000000000 : ℝ)) (alpha := (735440407379/337850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6755162113561794591/6757000000000000000 : ℝ)*(X 0 2+X 1 2)+(735440407379/337850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4247/1024 : ℝ)) (lo := (6369/100000 : ℝ)) (hi := (19883/100000 : ℝ)) (c := (6755162113561794591/6757000000000000000 : ℝ)) (alpha := (735440407379/337850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1039599707/5000000000 : ℝ)*X 0 0+(1099098883/2000000000 : ℝ)*X 0 1+(5170836497/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2684943381/5000000000 : ℝ)*X 1 0+(-56187141/250000000 : ℝ)*X 1 1+(8273339/16000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5369886959/10000000000 : ℝ)*X 2 0+(323177283/625000000 : ℝ)*X 2 1+(-2247485833/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2166578339/5000000000 : ℝ)*X 0 0+(200613061/500000000 : ℝ)*X 0 1+(4678497549/10000000000 : ℝ)*X 0 2+(2166578339/5000000000 : ℝ)*X 1 0+(200613061/500000000 : ℝ)*X 1 1+(4678497549/10000000000 : ℝ)*X 1 2+(2166578339/5000000000 : ℝ)*X 2 0+(200613061/500000000 : ℝ)*X 2 1+(4678497549/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-259910393/1250000000 : ℝ)*X 0 0+(323312621/625000000 : ℝ)*X 0 1+(2746654343/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1057343227/2000000000 : ℝ)*X 1 0+(-30078331/156250000 : ℝ)*X 1 1+(5493308831/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1321679077/2500000000 : ℝ)*X 2 0+(2746654347/5000000000 : ℝ)*X 2 1+(-120313321/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4333328349/10000000000 : ℝ)*X 0 0+(4674052423/10000000000 : ℝ)*X 0 1+(2008375597/5000000000 : ℝ)*X 0 2+(4333328349/10000000000 : ℝ)*X 1 0+(4674052423/10000000000 : ℝ)*X 1 1+(2008375597/5000000000 : ℝ)*X 1 2+(4333328349/10000000000 : ℝ)*X 2 0+(4674052423/10000000000 : ℝ)*X 2 1+(2008375597/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1288_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (726186485182798930370216289/168925000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (875139809/50000000000000 : ℝ)*(base19) + (106556963/6250000000000 : ℝ)*(base23) + (1700841/2000000000000 : ℝ)*(lower2) + (127722751/25000000000000 : ℝ)*(upper3) + (134984381/50000000000000 : ℝ)*(upper5) + (1145299113154893/50000000000000 : ℝ)*(major0) + (1145299113154893/50000000000000 : ℝ)*(major1) + (1145299113154893/50000000000000 : ℝ)*(major2) + (1540091190420327/50000000000000 : ℝ)*(sp0) + (770048652352457/25000000000000 : ℝ)*(sp1) + (77004866369451/2500000000000 : ℝ)*(sp2) + (1500983018453363/100000000000000 : ℝ)*(sp3) + (13978848793/100000000000000 : ℝ)*(sp4) + (3386236223/20000000000000 : ℝ)*(sp7) + (1500999949634477/100000000000000 : ℝ)*(f.failure) + (3080196359689447/100000000000000 : ℝ)*(f.sum) + (167088246822497/33785000000000000000000000000 : ℝ)*base66 + (128847154378026237/337850000000000000000000000000000 : ℝ)*base68 + (279254078967526237/337850000000000000000000000000000 : ℝ)*base70 + (360106588539273763/337850000000000000000000000000000 : ℝ)*base71 + (28302483282437/33785000000000000000000000000 : ℝ)*base74 + (228283629570073763/337850000000000000000000000000000 : ℝ)*base75 + (2351370556259126237/337850000000000000000000000000000 : ℝ)*base78 + (4406715497364726237/337850000000000000000000000000000 : ℝ)*base80 + (175004978343/33785000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (20524291/10000000000000000000000 : ℝ)*base90 + (20524291/10000000000000000000000 : ℝ)*base92 + (20524291/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1262934977552230930469152539/168925000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (141493727/10000000000000 : ℝ)*(base19) + (348801409/20000000000000 : ℝ)*(base23) + (219592379/100000000000000 : ℝ)*(upper3) + (10582879/12500000000000 : ℝ)*(lower4) + (50362017/50000000000000 : ℝ)*(upper5) + (1160844544035381/50000000000000 : ℝ)*(major0) + (1160844544035381/50000000000000 : ℝ)*(major1) + (1160844544035381/50000000000000 : ℝ)*(major2) + (14368542977/100000000000000 : ℝ)*(sp1) + (1861236377/10000000000000 : ℝ)*(sp2) + (1561002265066499/50000000000000 : ℝ)*(sp4) + (3121988746652751/100000000000000 : ℝ)*(sp5) + (390248021720273/12500000000000 : ℝ)*(sp6) + (760686698399161/50000000000000 : ℝ)*(sp7) + (760686698399161/50000000000000 : ℝ)*(f.failure) + (1561002265066499/50000000000000 : ℝ)*(f.sum) + (111980596067607/16892500000000000000000000000 : ℝ)*base66 + (565152383255495829/337850000000000000000000000000000 : ℝ)*base68 + (1033310709997195829/337850000000000000000000000000000 : ℝ)*base70 + (1484178677484045829/337850000000000000000000000000000 : ℝ)*base72 + (37190236076437/16892500000000000000000000000 : ℝ)*base74 + (3602322220811995829/337850000000000000000000000000000 : ℝ)*base76 + (1882626886981595829/337850000000000000000000000000000 : ℝ)*base78 + (3066571528400295829/337850000000000000000000000000000 : ℝ)*base80 + (32035865905953/16892500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (57358537/5000000000000000000000 : ℝ)*base89 + (57358537/5000000000000000000000 : ℝ)*base91 + (57358537/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1288_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152604817/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19883/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6369/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (379/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1288_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1288_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152604817/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (379/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1288_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1288_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1288_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4247/1024 : ℝ) ≤ p) (hpb : p ≤ (531/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152604817/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (379/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1021/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1288_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
