-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1278_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:20:52.352238+00:00
-- url     : https://prove2.me/submissions/18c7d3ab-a3a7-4b28-af4c-2632a4e1293a

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
theorem support_rectangle_w1278_s3_0 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1049013623/5000000000 : ℝ)*x 0 + (1087242623/2000000000 : ℝ)*x 1 + (2611943767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049013623/5000000000 : ℝ)^2119 ≤ (12756631553717/100000000000000 : ℝ)^1607 := by
    have hnat : (1049013623 : ℕ)^2119*100000000000000^1607 ≤ 12756631553717^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049013623 5000000000 12756631553717 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1087242623/2000000000 : ℝ)^2119 ≤ (44767239623271/100000000000000 : ℝ)^1607 := by
    have hnat : (1087242623 : ℕ)^2119*100000000000000^1607 ≤ 44767239623271^1607*2000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087242623 2000000000 44767239623271 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2611943767/5000000000 : ℝ)^2119 ≤ (10619032202289/25000000000000 : ℝ)^1607 := by
    have hnat : (2611943767 : ℕ)^2119*25000000000000^1607 ≤ 10619032202289^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2611943767 5000000000 10619032202289 25000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1049013623/5000000000 : ℝ), (1087242623/2000000000 : ℝ), (2611943767/5000000000 : ℝ)] ![(12756631553717/100000000000000 : ℝ), (44767239623271/100000000000000 : ℝ), (10619032202289/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1049013623/5000000000 : ℝ)|^2119 ≤ (12756631553717/100000000000000 : ℝ)^1607
        have hw : |(-1049013623/5000000000 : ℝ)|=(1049013623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1087242623/2000000000 : ℝ)|^2119 ≤ (44767239623271/100000000000000 : ℝ)^1607
        have hw : |(1087242623/2000000000 : ℝ)|=(1087242623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2611943767/5000000000 : ℝ)|^2119 ≤ (10619032202289/25000000000000 : ℝ)^1607
        have hw : |(2611943767/5000000000 : ℝ)|=(2611943767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s3_1 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1338774153/2500000000 : ℝ)*x 0 + (-1103370217/5000000000 : ℝ)*x 1 + (5223887459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338774153/2500000000 : ℝ)^2119 ≤ (43888518538059/100000000000000 : ℝ)^1607 := by
    have hnat : (1338774153 : ℕ)^2119*100000000000000^1607 ≤ 43888518538059^1607*2500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338774153 2500000000 43888518538059 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1103370217/5000000000 : ℝ)^2119 ≤ (3408838360073/25000000000000 : ℝ)^1607 := by
    have hnat : (1103370217 : ℕ)^2119*25000000000000^1607 ≤ 3408838360073^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103370217 5000000000 3408838360073 25000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5223887459/10000000000 : ℝ)^2119 ≤ (1327379000157/3125000000000 : ℝ)^1607 := by
    have hnat : (5223887459 : ℕ)^2119*3125000000000^1607 ≤ 1327379000157^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223887459 10000000000 1327379000157 3125000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338774153/2500000000 : ℝ), (-1103370217/5000000000 : ℝ), (5223887459/10000000000 : ℝ)] ![(43888518538059/100000000000000 : ℝ), (3408838360073/25000000000000 : ℝ), (1327379000157/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338774153/2500000000 : ℝ)|^2119 ≤ (43888518538059/100000000000000 : ℝ)^1607
        have hw : |(1338774153/2500000000 : ℝ)|=(1338774153/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1103370217/5000000000 : ℝ)|^2119 ≤ (3408838360073/25000000000000 : ℝ)^1607
        have hw : |(-1103370217/5000000000 : ℝ)|=(1103370217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5223887459/10000000000 : ℝ)|^2119 ≤ (1327379000157/3125000000000 : ℝ)^1607
        have hw : |(5223887459/10000000000 : ℝ)|=(5223887459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s3_2 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1338774133/2500000000 : ℝ)*x 0 + (5223887883/10000000000 : ℝ)*x 1 + (-2206739983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338774133/2500000000 : ℝ)^2119 ≤ (5486064709189/12500000000000 : ℝ)^1607 := by
    have hnat : (1338774133 : ℕ)^2119*12500000000000^1607 ≤ 5486064709189^1607*2500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338774133 2500000000 5486064709189 12500000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5223887883/10000000000 : ℝ)^2119 ≤ (10619033137763/25000000000000 : ℝ)^1607 := by
    have hnat : (5223887883 : ℕ)^2119*25000000000000^1607 ≤ 10619033137763^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5223887883 10000000000 10619033137763 25000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2206739983/10000000000 : ℝ)^2119 ≤ (340883744143/2500000000000 : ℝ)^1607 := by
    have hnat : (2206739983 : ℕ)^2119*2500000000000^1607 ≤ 340883744143^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206739983 10000000000 340883744143 2500000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338774133/2500000000 : ℝ), (5223887883/10000000000 : ℝ), (-2206739983/10000000000 : ℝ)] ![(5486064709189/12500000000000 : ℝ), (10619033137763/25000000000000 : ℝ), (340883744143/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338774133/2500000000 : ℝ)|^2119 ≤ (5486064709189/12500000000000 : ℝ)^1607
        have hw : |(1338774133/2500000000 : ℝ)|=(1338774133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5223887883/10000000000 : ℝ)|^2119 ≤ (10619033137763/25000000000000 : ℝ)^1607
        have hw : |(5223887883/10000000000 : ℝ)|=(5223887883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2206739983/10000000000 : ℝ)|^2119 ≤ (340883744143/2500000000000 : ℝ)^1607
        have hw : |(-2206739983/10000000000 : ℝ)|=(2206739983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s3_3 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1085525063/2500000000 : ℝ)*x 0 + (4130291469/10000000000 : ℝ)*x 1 + (182573481/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085525063/2500000000 : ℝ)^2119 ≤ (6657310355401/20000000000000 : ℝ)^1607 := by
    have hnat : (1085525063 : ℕ)^2119*20000000000000^1607 ≤ 6657310355401^1607*2500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085525063 2500000000 6657310355401 20000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4130291469/10000000000 : ℝ)^2119 ≤ (31162321908873/100000000000000 : ℝ)^1607 := by
    have hnat : (4130291469 : ℕ)^2119*100000000000000^1607 ≤ 31162321908873^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4130291469 10000000000 31162321908873 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (182573481/400000000 : ℝ)^2119 ≤ (35551126297131/100000000000000 : ℝ)^1607 := by
    have hnat : (182573481 : ℕ)^2119*100000000000000^1607 ≤ 35551126297131^1607*400000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182573481 400000000 35551126297131 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1085525063/2500000000 : ℝ), (4130291469/10000000000 : ℝ), (182573481/400000000 : ℝ)] ![(6657310355401/20000000000000 : ℝ), (31162321908873/100000000000000 : ℝ), (35551126297131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1085525063/2500000000 : ℝ)|^2119 ≤ (6657310355401/20000000000000 : ℝ)^1607
        have hw : |(1085525063/2500000000 : ℝ)|=(1085525063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4130291469/10000000000 : ℝ)|^2119 ≤ (31162321908873/100000000000000 : ℝ)^1607
        have hw : |(4130291469/10000000000 : ℝ)|=(4130291469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(182573481/400000000 : ℝ)|^2119 ≤ (35551126297131/100000000000000 : ℝ)^1607
        have hw : |(182573481/400000000 : ℝ)|=(182573481/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s3_4 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2098050911/10000000000 : ℝ)*x 0 + (5224811627/10000000000 : ℝ)*x 1 + (2717641577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2098050911/10000000000 : ℝ)^2119 ≤ (1594602661079/12500000000000 : ℝ)^1607 := by
    have hnat : (2098050911 : ℕ)^2119*12500000000000^1607 ≤ 1594602661079^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098050911 10000000000 1594602661079 12500000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5224811627/10000000000 : ℝ)^2119 ≤ (42486036994207/100000000000000 : ℝ)^1607 := by
    have hnat : (5224811627 : ℕ)^2119*100000000000000^1607 ≤ 42486036994207^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5224811627 10000000000 42486036994207 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2717641577/5000000000 : ℝ)^2119 ≤ (11189285426419/25000000000000 : ℝ)^1607 := by
    have hnat : (2717641577 : ℕ)^2119*25000000000000^1607 ≤ 11189285426419^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717641577 5000000000 11189285426419 25000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2098050911/10000000000 : ℝ), (5224811627/10000000000 : ℝ), (2717641577/5000000000 : ℝ)] ![(1594602661079/12500000000000 : ℝ), (42486036994207/100000000000000 : ℝ), (11189285426419/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2098050911/10000000000 : ℝ)|^2119 ≤ (1594602661079/12500000000000 : ℝ)^1607
        have hw : |(-2098050911/10000000000 : ℝ)|=(2098050911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5224811627/10000000000 : ℝ)|^2119 ≤ (42486036994207/100000000000000 : ℝ)^1607
        have hw : |(5224811627/10000000000 : ℝ)|=(5224811627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2717641577/5000000000 : ℝ)|^2119 ≤ (11189285426419/25000000000000 : ℝ)^1607
        have hw : |(2717641577/5000000000 : ℝ)|=(2717641577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s3_5 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5300827967/10000000000 : ℝ)*x 0 + (-24941809/125000000 : ℝ)*x 1 + (1358820771/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5300827967/10000000000 : ℝ)^2119 ≤ (21651497496983/50000000000000 : ℝ)^1607 := by
    have hnat : (5300827967 : ℕ)^2119*50000000000000^1607 ≤ 21651497496983^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5300827967 10000000000 21651497496983 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (24941809/125000000 : ℝ)^2119 ≤ (5969932025527/50000000000000 : ℝ)^1607 := by
    have hnat : (24941809 : ℕ)^2119*50000000000000^1607 ≤ 5969932025527^1607*125000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24941809 125000000 5969932025527 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358820771/2500000000 : ℝ)^2119 ≤ (22378570472803/50000000000000 : ℝ)^1607 := by
    have hnat : (1358820771 : ℕ)^2119*50000000000000^1607 ≤ 22378570472803^1607*2500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358820771 2500000000 22378570472803 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5300827967/10000000000 : ℝ), (-24941809/125000000 : ℝ), (1358820771/2500000000 : ℝ)] ![(21651497496983/50000000000000 : ℝ), (5969932025527/50000000000000 : ℝ), (22378570472803/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5300827967/10000000000 : ℝ)|^2119 ≤ (21651497496983/50000000000000 : ℝ)^1607
        have hw : |(5300827967/10000000000 : ℝ)|=(5300827967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-24941809/125000000 : ℝ)|^2119 ≤ (5969932025527/50000000000000 : ℝ)^1607
        have hw : |(-24941809/125000000 : ℝ)|=(24941809/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358820771/2500000000 : ℝ)|^2119 ≤ (22378570472803/50000000000000 : ℝ)^1607
        have hw : |(1358820771/2500000000 : ℝ)|=(1358820771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s3_6 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5300827973/10000000000 : ℝ)*x 0 + (5435283067/10000000000 : ℝ)*x 1 + (-399068947/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5300827973/10000000000 : ℝ)^2119 ≤ (43302995058597/100000000000000 : ℝ)^1607 := by
    have hnat : (5300827973 : ℕ)^2119*100000000000000^1607 ≤ 43302995058597^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5300827973 10000000000 43302995058597 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435283067/10000000000 : ℝ)^2119 ≤ (22378570380509/50000000000000 : ℝ)^1607 := by
    have hnat : (5435283067 : ℕ)^2119*50000000000000^1607 ≤ 22378570380509^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435283067 10000000000 22378570380509 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (399068947/2000000000 : ℝ)^2119 ≤ (1193986416941/10000000000000 : ℝ)^1607 := by
    have hnat : (399068947 : ℕ)^2119*10000000000000^1607 ≤ 1193986416941^1607*2000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399068947 2000000000 1193986416941 10000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5300827973/10000000000 : ℝ), (5435283067/10000000000 : ℝ), (-399068947/2000000000 : ℝ)] ![(43302995058597/100000000000000 : ℝ), (22378570380509/50000000000000 : ℝ), (1193986416941/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5300827973/10000000000 : ℝ)|^2119 ≤ (43302995058597/100000000000000 : ℝ)^1607
        have hw : |(5300827973/10000000000 : ℝ)|=(5300827973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435283067/10000000000 : ℝ)|^2119 ≤ (22378570380509/50000000000000 : ℝ)^1607
        have hw : |(5435283067/10000000000 : ℝ)|=(5435283067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-399068947/2000000000 : ℝ)|^2119 ≤ (1193986416941/10000000000000 : ℝ)^1607
        have hw : |(-399068947/2000000000 : ℝ)|=(399068947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s3_7 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4342148809/10000000000 : ℝ)*x 0 + (4562447939/10000000000 : ℝ)*x 1 + (4132192061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4342148809/10000000000 : ℝ)^2119 ≤ (8321760653323/25000000000000 : ℝ)^1607 := by
    have hnat : (4342148809 : ℕ)^2119*25000000000000^1607 ≤ 8321760653323^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4342148809 10000000000 8321760653323 25000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4562447939/10000000000 : ℝ)^2119 ≤ (7106345151311/20000000000000 : ℝ)^1607 := by
    have hnat : (4562447939 : ℕ)^2119*20000000000000^1607 ≤ 7106345151311^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4562447939 10000000000 7106345151311 20000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4132192061/10000000000 : ℝ)^2119 ≤ (31181231621003/100000000000000 : ℝ)^1607 := by
    have hnat : (4132192061 : ℕ)^2119*100000000000000^1607 ≤ 31181231621003^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4132192061 10000000000 31181231621003 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4342148809/10000000000 : ℝ), (4562447939/10000000000 : ℝ), (4132192061/10000000000 : ℝ)] ![(8321760653323/25000000000000 : ℝ), (7106345151311/20000000000000 : ℝ), (31181231621003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4342148809/10000000000 : ℝ)|^2119 ≤ (8321760653323/25000000000000 : ℝ)^1607
        have hw : |(4342148809/10000000000 : ℝ)|=(4342148809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4562447939/10000000000 : ℝ)|^2119 ≤ (7106345151311/20000000000000 : ℝ)^1607
        have hw : |(4562447939/10000000000 : ℝ)|=(4562447939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4132192061/10000000000 : ℝ)|^2119 ≤ (31181231621003/100000000000000 : ℝ)^1607
        have hw : |(4132192061/10000000000 : ℝ)|=(4132192061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1278_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152212411/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16383/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (47/500 : ℝ)*pair X i i ≤ pair X i h) :
    (5297/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7543/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16383/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (47/500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16383/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (47/500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16383/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (47/500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16383/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (47/500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16383/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (47/500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16383/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (47/500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (47/500 : ℝ) ^ (4237/1024 : ℝ) ≤ (176183792779343/3125000000000000000 : ℝ) := by
    have hpowers : (47/500 : ℝ)^4237 ≤ (176183792779343/3125000000000000000 : ℝ)^1024 := by
      have hnat : (47 : ℕ)^4237*3125000000000000000^1024 ≤ 176183792779343^1024*500^4237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        47 500 176183792779343 3125000000000000000 4237 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (47/500 : ℝ)) (X := (176183792779343/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16383/100000 : ℝ) ^ (4237/1024 : ℝ) ≤ (28078208029569657/50000000000000000000 : ℝ) := by
    have hpowers : (16383/100000 : ℝ)^4237 ≤ (28078208029569657/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16383 : ℕ)^4237*50000000000000000000^1024 ≤ 28078208029569657^1024*100000^4237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16383 100000 28078208029569657 50000000000000000000 4237 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16383/100000 : ℝ)) (X := (28078208029569657/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562676183792779343/1562500000000000000 : ℝ) ≤ (2000054500294699/2000000000000000 : ℝ) ^ (4237/1024 : ℝ) := by
    have hpowers : (1562676183792779343/1562500000000000000 : ℝ)^1024 ≤ (2000054500294699/2000000000000000 : ℝ)^4237 := by
      have hnat : (1562676183792779343 : ℕ)^1024*2000000000000000^4237 ≤ 2000054500294699^4237*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562676183792779343 1562500000000000000 2000054500294699 2000000000000000 1024 4237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000054500294699/2000000000000000 : ℝ)) (X := (1562676183792779343/1562500000000000000 : ℝ)) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10006179429742807829/10000000000000000000 : ℝ) ≤ (10001493097477073/10000000000000000 : ℝ) ^ (4237/1024 : ℝ) := by
    have hpowers : (10006179429742807829/10000000000000000000 : ℝ)^1024 ≤ (10001493097477073/10000000000000000 : ℝ)^4237 := by
      have hnat : (10006179429742807829 : ℕ)^1024*10000000000000000^4237 ≤ 10001493097477073^4237*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006179429742807829 10000000000000000000 10001493097477073 10000000000000000 1024 4237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001493097477073/10000000000000000 : ℝ)) (X := (10006179429742807829/10000000000000000000 : ℝ)) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25028078208029569657/25000000000000000000 : ℝ) ≤ (10002713693480651/10000000000000000 : ℝ) ^ (4237/1024 : ℝ) := by
    have hpowers : (25028078208029569657/25000000000000000000 : ℝ)^1024 ≤ (10002713693480651/10000000000000000 : ℝ)^4237 := by
      have hnat : (25028078208029569657 : ℕ)^1024*10000000000000000^4237 ≤ 10002713693480651^4237*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25028078208029569657 25000000000000000000 10002713693480651 10000000000000000 1024 4237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002713693480651/10000000000000000 : ℝ)) (X := (25028078208029569657/25000000000000000000 : ℝ)) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(176183792779343/3125000000000000000 : ℝ) ≤ ((13961791134584429837/13966000000000000000 : ℝ)+2*(610298001789/349150000000000 : ℝ)*(47/500 : ℝ))^(4237/1024 : ℝ) := by
    rw [show (13961791134584429837/13966000000000000000 : ℝ)+2*(610298001789/349150000000000 : ℝ)*(47/500 : ℝ)=(2000054500294699/2000000000000000 : ℝ) by norm_num, show 1+2*(176183792779343/3125000000000000000 : ℝ)=(1562676183792779343/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28078208029569657/50000000000000000000 : ℝ)+(176183792779343/3125000000000000000 : ℝ) ≤ ((13961791134584429837/13966000000000000000 : ℝ)+(610298001789/349150000000000 : ℝ)*((16383/100000 : ℝ)+(47/500 : ℝ)))^(4237/1024 : ℝ) := by
    rw [show (13961791134584429837/13966000000000000000 : ℝ)+(610298001789/349150000000000 : ℝ)*((16383/100000 : ℝ)+(47/500 : ℝ))=(10001493097477073/10000000000000000 : ℝ) by norm_num, show 1+(28078208029569657/50000000000000000000 : ℝ)+(176183792779343/3125000000000000000 : ℝ)=(10006179429742807829/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28078208029569657/50000000000000000000 : ℝ) ≤ ((13961791134584429837/13966000000000000000 : ℝ)+2*(610298001789/349150000000000 : ℝ)*(16383/100000 : ℝ))^(4237/1024 : ℝ) := by
    rw [show (13961791134584429837/13966000000000000000 : ℝ)+2*(610298001789/349150000000000 : ℝ)*(16383/100000 : ℝ)=(10002713693480651/10000000000000000 : ℝ) by norm_num, show 1+2*(28078208029569657/50000000000000000000 : ℝ)=(25028078208029569657/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13961791134584429837/13966000000000000000 : ℝ)*(X 1 0+X 2 0)+(610298001789/349150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4237/1024 : ℝ)) (lo := (47/500 : ℝ)) (hi := (16383/100000 : ℝ)) (c := (13961791134584429837/13966000000000000000 : ℝ)) (alpha := (610298001789/349150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13961791134584429837/13966000000000000000 : ℝ)*(X 0 1+X 2 1)+(610298001789/349150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4237/1024 : ℝ)) (lo := (47/500 : ℝ)) (hi := (16383/100000 : ℝ)) (c := (13961791134584429837/13966000000000000000 : ℝ)) (alpha := (610298001789/349150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13961791134584429837/13966000000000000000 : ℝ)*(X 0 2+X 1 2)+(610298001789/349150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4237/1024 : ℝ)) (lo := (47/500 : ℝ)) (hi := (16383/100000 : ℝ)) (c := (13961791134584429837/13966000000000000000 : ℝ)) (alpha := (610298001789/349150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1049013623/5000000000 : ℝ)*X 0 0+(1087242623/2000000000 : ℝ)*X 0 1+(2611943767/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338774153/2500000000 : ℝ)*X 1 0+(-1103370217/5000000000 : ℝ)*X 1 1+(5223887459/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338774133/2500000000 : ℝ)*X 2 0+(5223887883/10000000000 : ℝ)*X 2 1+(-2206739983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1085525063/2500000000 : ℝ)*X 0 0+(4130291469/10000000000 : ℝ)*X 0 1+(182573481/400000000 : ℝ)*X 0 2+(1085525063/2500000000 : ℝ)*X 1 0+(4130291469/10000000000 : ℝ)*X 1 1+(182573481/400000000 : ℝ)*X 1 2+(1085525063/2500000000 : ℝ)*X 2 0+(4130291469/10000000000 : ℝ)*X 2 1+(182573481/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2098050911/10000000000 : ℝ)*X 0 0+(5224811627/10000000000 : ℝ)*X 0 1+(2717641577/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5300827967/10000000000 : ℝ)*X 1 0+(-24941809/125000000 : ℝ)*X 1 1+(1358820771/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5300827973/10000000000 : ℝ)*X 2 0+(5435283067/10000000000 : ℝ)*X 2 1+(-399068947/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4342148809/10000000000 : ℝ)*X 0 0+(4562447939/10000000000 : ℝ)*X 0 1+(4132192061/10000000000 : ℝ)*X 0 2+(4342148809/10000000000 : ℝ)*X 1 0+(4562447939/10000000000 : ℝ)*X 1 1+(4132192061/10000000000 : ℝ)*X 1 2+(4342148809/10000000000 : ℝ)*X 2 0+(4562447939/10000000000 : ℝ)*X 2 1+(4132192061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3301577351072510080260720867/349150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (108786951/6250000000000 : ℝ)*(base19) + (1684942293/100000000000000 : ℝ)*(base23) + (3364179/50000000000000 : ℝ)*(lower2) + (311047657/100000000000000 : ℝ)*(upper5) + (3506878398164603/100000000000000 : ℝ)*(major0) + (3506878398164603/100000000000000 : ℝ)*(major1) + (3506878398164603/100000000000000 : ℝ)*(major2) + (4709778909966033/100000000000000 : ℝ)*(sp0) + (4709814824001257/100000000000000 : ℝ)*(sp1) + (4709817571142379/100000000000000 : ℝ)*(sp2) + (1151961649839917/50000000000000 : ℝ)*(sp3) + (40346118639/100000000000000 : ℝ)*(sp4) + (2691492199/100000000000000 : ℝ)*(sp5) + (13925363269/100000000000000 : ℝ)*(sp7) + (2303937225043103/100000000000000 : ℝ)*(f.failure) + (73590925876323/1562500000000 : ℝ)*(f.sum) + (19159662297651/8728750000000000000000000000 : ℝ)*base65 + (7101090054450139711/1396600000000000000000000000000000 : ℝ)*base67 + (8160586983596939711/1396600000000000000000000000000000 : ℝ)*base69 + (10993751783341539711/1396600000000000000000000000000000 : ℝ)*base71 + (23656031317649/34915000000000000000000000000 : ℝ)*base73 + (4542055528210339711/1396600000000000000000000000000000 : ℝ)*base75 + (172287151761060289/1396600000000000000000000000000000 : ℝ)*base78 + (4366330489560739711/1396600000000000000000000000000000 : ℝ)*base79 + (11522249056051/8728750000000000000000000000 : ℝ)*base81 + (13448667/10000000000000000000000 : ℝ)*base90 + (13448667/10000000000000000000000 : ℝ)*base92 + (13448667/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (735573478253806577594623377/69830000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2288964229/100000000000000 : ℝ)*(base19) + (601642291/25000000000000 : ℝ)*(base23) + (227640061/100000000000000 : ℝ)*(upper3) + (55576347/100000000000000 : ℝ)*(lower4) + (259015519/100000000000000 : ℝ)*(upper5) + (353771726766269/10000000000000 : ℝ)*(major0) + (353771726766269/10000000000000 : ℝ)*(major1) + (353771726766269/10000000000000 : ℝ)*(major2) + (4635553933/12500000000000 : ℝ)*(sp1) + (4725697831/12500000000000 : ℝ)*(sp2) + (593904567744613/12500000000000 : ℝ)*(sp4) + (475119716856121/10000000000000 : ℝ)*(sp5) + (1187799082451273/25000000000000 : ℝ)*(sp6) + (2324197642242649/100000000000000 : ℝ)*(sp7) + (2324197642242649/100000000000000 : ℝ)*(f.failure) + (593904567744613/12500000000000 : ℝ)*(f.sum) + (15728685994587/6983000000000000000000000000 : ℝ)*base66 + (808693628427131847/139660000000000000000000000000000 : ℝ)*base68 + (1040128625727891847/139660000000000000000000000000000 : ℝ)*base70 + (1603714024594731847/139660000000000000000000000000000 : ℝ)*base72 + (18469799981159/6983000000000000000000000000 : ℝ)*base73 + (448107986351891847/139660000000000000000000000000000 : ℝ)*base76 + (1313731711781971847/139660000000000000000000000000000 : ℝ)*base78 + (2658924467123531847/139660000000000000000000000000000 : ℝ)*base80 + (24088460393709/6983000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (51316739/10000000000000000000000 : ℝ)*base89 + (51316739/10000000000000000000000 : ℝ)*base91 + (51316739/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1278_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152212411/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16383/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (47/500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5297/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7543/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1278_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1278_s4_0 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2100099837/10000000000 : ℝ)*x 0 + (2710017431/5000000000 : ℝ)*x 1 + (5238707903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2100099837/10000000000 : ℝ)^2119 ≤ (12773251204771/100000000000000 : ℝ)^1607 := by
    have hnat : (2100099837 : ℕ)^2119*100000000000000^1607 ≤ 12773251204771^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100099837 10000000000 12773251204771 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2710017431/5000000000 : ℝ)^2119 ≤ (8918329545889/20000000000000 : ℝ)^1607 := by
    have hnat : (2710017431 : ℕ)^2119*20000000000000^1607 ≤ 8918329545889^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710017431 5000000000 8918329545889 20000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5238707903/10000000000 : ℝ)^2119 ≤ (42635101057283/100000000000000 : ℝ)^1607 := by
    have hnat : (5238707903 : ℕ)^2119*100000000000000^1607 ≤ 42635101057283^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238707903 10000000000 42635101057283 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2100099837/10000000000 : ℝ), (2710017431/5000000000 : ℝ), (5238707903/10000000000 : ℝ)] ![(12773251204771/100000000000000 : ℝ), (8918329545889/20000000000000 : ℝ), (42635101057283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2100099837/10000000000 : ℝ)|^2119 ≤ (12773251204771/100000000000000 : ℝ)^1607
        have hw : |(-2100099837/10000000000 : ℝ)|=(2100099837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2710017431/5000000000 : ℝ)|^2119 ≤ (8918329545889/20000000000000 : ℝ)^1607
        have hw : |(2710017431/5000000000 : ℝ)|=(2710017431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5238707903/10000000000 : ℝ)|^2119 ≤ (42635101057283/100000000000000 : ℝ)^1607
        have hw : |(5238707903/10000000000 : ℝ)|=(5238707903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s4_1 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337754349/2500000000 : ℝ)*x 0 + (-1096312199/5000000000 : ℝ)*x 1 + (5238707867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337754349/2500000000 : ℝ)^2119 ≤ (21922220228451/50000000000000 : ℝ)^1607 := by
    have hnat : (1337754349 : ℕ)^2119*50000000000000^1607 ≤ 21922220228451^1607*2500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337754349 2500000000 21922220228451 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1096312199/5000000000 : ℝ)^2119 ≤ (338011471417/2500000000000 : ℝ)^1607 := by
    have hnat : (1096312199 : ℕ)^2119*2500000000000^1607 ≤ 338011471417^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096312199 5000000000 338011471417 2500000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5238707867/10000000000 : ℝ)^2119 ≤ (42635100670951/100000000000000 : ℝ)^1607 := by
    have hnat : (5238707867 : ℕ)^2119*100000000000000^1607 ≤ 42635100670951^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238707867 10000000000 42635100670951 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337754349/2500000000 : ℝ), (-1096312199/5000000000 : ℝ), (5238707867/10000000000 : ℝ)] ![(21922220228451/50000000000000 : ℝ), (338011471417/2500000000000 : ℝ), (42635100670951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337754349/2500000000 : ℝ)|^2119 ≤ (21922220228451/50000000000000 : ℝ)^1607
        have hw : |(1337754349/2500000000 : ℝ)|=(1337754349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1096312199/5000000000 : ℝ)|^2119 ≤ (338011471417/2500000000000 : ℝ)^1607
        have hw : |(-1096312199/5000000000 : ℝ)|=(1096312199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5238707867/10000000000 : ℝ)|^2119 ≤ (42635100670951/100000000000000 : ℝ)^1607
        have hw : |(5238707867/10000000000 : ℝ)|=(5238707867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s4_2 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5351017089/10000000000 : ℝ)*x 0 + (5238708133/10000000000 : ℝ)*x 1 + (-438524891/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351017089/10000000000 : ℝ)^2119 ≤ (5480554642501/12500000000000 : ℝ)^1607 := by
    have hnat : (5351017089 : ℕ)^2119*12500000000000^1607 ≤ 5480554642501^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351017089 10000000000 5480554642501 12500000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5238708133/10000000000 : ℝ)^2119 ≤ (8527020705103/20000000000000 : ℝ)^1607 := by
    have hnat : (5238708133 : ℕ)^2119*20000000000000^1607 ≤ 8527020705103^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5238708133 10000000000 8527020705103 20000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (438524891/2000000000 : ℝ)^2119 ≤ (2704091864029/20000000000000 : ℝ)^1607 := by
    have hnat : (438524891 : ℕ)^2119*20000000000000^1607 ≤ 2704091864029^1607*2000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438524891 2000000000 2704091864029 20000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351017089/10000000000 : ℝ), (5238708133/10000000000 : ℝ), (-438524891/2000000000 : ℝ)] ![(5480554642501/12500000000000 : ℝ), (8527020705103/20000000000000 : ℝ), (2704091864029/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351017089/10000000000 : ℝ)|^2119 ≤ (5480554642501/12500000000000 : ℝ)^1607
        have hw : |(5351017089/10000000000 : ℝ)|=(5351017089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5238708133/10000000000 : ℝ)|^2119 ≤ (8527020705103/20000000000000 : ℝ)^1607
        have hw : |(5238708133/10000000000 : ℝ)|=(5238708133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-438524891/2000000000 : ℝ)|^2119 ≤ (2704091864029/20000000000000 : ℝ)^1607
        have hw : |(-438524891/2000000000 : ℝ)|=(438524891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s4_3 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (108583801/250000000 : ℝ)*x 0 + (2080908727/5000000000 : ℝ)*x 1 + (453249431/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108583801/250000000 : ℝ)^2119 ≤ (6659841195837/20000000000000 : ℝ)^1607 := by
    have hnat : (108583801 : ℕ)^2119*20000000000000^1607 ≤ 6659841195837^1607*250000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108583801 250000000 6659841195837 20000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2080908727/5000000000 : ℝ)^2119 ≤ (1573817181783/5000000000000 : ℝ)^1607 := by
    have hnat : (2080908727 : ℕ)^2119*5000000000000^1607 ≤ 1573817181783^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2080908727 5000000000 1573817181783 5000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (453249431/1000000000 : ℝ)^2119 ≤ (35224450369101/100000000000000 : ℝ)^1607 := by
    have hnat : (453249431 : ℕ)^2119*100000000000000^1607 ≤ 35224450369101^1607*1000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453249431 1000000000 35224450369101 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108583801/250000000 : ℝ), (2080908727/5000000000 : ℝ), (453249431/1000000000 : ℝ)] ![(6659841195837/20000000000000 : ℝ), (1573817181783/5000000000000 : ℝ), (35224450369101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108583801/250000000 : ℝ)|^2119 ≤ (6659841195837/20000000000000 : ℝ)^1607
        have hw : |(108583801/250000000 : ℝ)|=(108583801/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2080908727/5000000000 : ℝ)|^2119 ≤ (1573817181783/5000000000000 : ℝ)^1607
        have hw : |(2080908727/5000000000 : ℝ)|=(2080908727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(453249431/1000000000 : ℝ)|^2119 ≤ (35224450369101/100000000000000 : ℝ)^1607
        have hw : |(453249431/1000000000 : ℝ)|=(453249431/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s4_4 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2100114959/10000000000 : ℝ)*x 0 + (523938239/1000000000 : ℝ)*x 1 + (5419356441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2100114959/10000000000 : ℝ)^2119 ≤ (12773372483971/100000000000000 : ℝ)^1607 := by
    have hnat : (2100114959 : ℕ)^2119*100000000000000^1607 ≤ 12773372483971^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100114959 10000000000 12773372483971 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523938239/1000000000 : ℝ)^2119 ≤ (42642339425691/100000000000000 : ℝ)^1607 := by
    have hnat : (523938239 : ℕ)^2119*100000000000000^1607 ≤ 42642339425691^1607*1000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523938239 1000000000 42642339425691 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419356441/10000000000 : ℝ)^2119 ≤ (44584288079753/100000000000000 : ℝ)^1607 := by
    have hnat : (5419356441 : ℕ)^2119*100000000000000^1607 ≤ 44584288079753^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419356441 10000000000 44584288079753 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2100114959/10000000000 : ℝ), (523938239/1000000000 : ℝ), (5419356441/10000000000 : ℝ)] ![(12773372483971/100000000000000 : ℝ), (42642339425691/100000000000000 : ℝ), (44584288079753/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2100114959/10000000000 : ℝ)|^2119 ≤ (12773372483971/100000000000000 : ℝ)^1607
        have hw : |(-2100114959/10000000000 : ℝ)|=(2100114959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(523938239/1000000000 : ℝ)|^2119 ≤ (42642339425691/100000000000000 : ℝ)^1607
        have hw : |(523938239/1000000000 : ℝ)|=(523938239/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419356441/10000000000 : ℝ)|^2119 ≤ (44584288079753/100000000000000 : ℝ)^1607
        have hw : |(5419356441/10000000000 : ℝ)|=(5419356441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s4_5 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5304675849/10000000000 : ℝ)*x 0 + (-2011975709/10000000000 : ℝ)*x 1 + (5419356537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304675849/10000000000 : ℝ)^2119 ≤ (43344448499259/100000000000000 : ℝ)^1607 := by
    have hnat : (5304675849 : ℕ)^2119*100000000000000^1607 ≤ 43344448499259^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304675849 10000000000 43344448499259 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2011975709/10000000000 : ℝ)^2119 ≤ (1207126236063/10000000000000 : ℝ)^1607 := by
    have hnat : (2011975709 : ℕ)^2119*10000000000000^1607 ≤ 1207126236063^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011975709 10000000000 1207126236063 10000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419356537/10000000000 : ℝ)^2119 ≤ (1114607228029/2500000000000 : ℝ)^1607 := by
    have hnat : (5419356537 : ℕ)^2119*2500000000000^1607 ≤ 1114607228029^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419356537 10000000000 1114607228029 2500000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304675849/10000000000 : ℝ), (-2011975709/10000000000 : ℝ), (5419356537/10000000000 : ℝ)] ![(43344448499259/100000000000000 : ℝ), (1207126236063/10000000000000 : ℝ), (1114607228029/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304675849/10000000000 : ℝ)|^2119 ≤ (43344448499259/100000000000000 : ℝ)^1607
        have hw : |(5304675849/10000000000 : ℝ)|=(5304675849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2011975709/10000000000 : ℝ)|^2119 ≤ (1207126236063/10000000000000 : ℝ)^1607
        have hw : |(-2011975709/10000000000 : ℝ)|=(2011975709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419356537/10000000000 : ℝ)|^2119 ≤ (1114607228029/2500000000000 : ℝ)^1607
        have hw : |(5419356537/10000000000 : ℝ)|=(5419356537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s4_6 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652337887/5000000000 : ℝ)*x 0 + (1354839101/2500000000 : ℝ)*x 1 + (-2011975993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652337887/5000000000 : ℝ)^2119 ≤ (8668889538237/20000000000000 : ℝ)^1607 := by
    have hnat : (2652337887 : ℕ)^2119*20000000000000^1607 ≤ 8668889538237^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652337887 5000000000 8668889538237 20000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354839101/2500000000 : ℝ)^2119 ≤ (44584287678377/100000000000000 : ℝ)^1607 := by
    have hnat : (1354839101 : ℕ)^2119*100000000000000^1607 ≤ 44584287678377^1607*2500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354839101 2500000000 44584287678377 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2011975993/10000000000 : ℝ)^2119 ≤ (482850584297/4000000000000 : ℝ)^1607 := by
    have hnat : (2011975993 : ℕ)^2119*4000000000000^1607 ≤ 482850584297^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011975993 10000000000 482850584297 4000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652337887/5000000000 : ℝ), (1354839101/2500000000 : ℝ), (-2011975993/10000000000 : ℝ)] ![(8668889538237/20000000000000 : ℝ), (44584287678377/100000000000000 : ℝ), (482850584297/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652337887/5000000000 : ℝ)|^2119 ≤ (8668889538237/20000000000000 : ℝ)^1607
        have hw : |(2652337887/5000000000 : ℝ)|=(2652337887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354839101/2500000000 : ℝ)|^2119 ≤ (44584287678377/100000000000000 : ℝ)^1607
        have hw : |(1354839101/2500000000 : ℝ)|=(1354839101/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2011975993/10000000000 : ℝ)|^2119 ≤ (482850584297/4000000000000 : ℝ)^1607
        have hw : |(-2011975993/10000000000 : ℝ)|=(2011975993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s4_7 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4343382307/10000000000 : ℝ)*x 0 + (4531115021/10000000000 : ℝ)*x 1 + (4163203927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4343382307/10000000000 : ℝ)^2119 ≤ (3329951195971/10000000000000 : ℝ)^1607 := by
    have hnat : (4343382307 : ℕ)^2119*10000000000000^1607 ≤ 3329951195971^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4343382307 10000000000 3329951195971 10000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4531115021/10000000000 : ℝ)^2119 ≤ (17605158328271/50000000000000 : ℝ)^1607 := by
    have hnat : (4531115021 : ℕ)^2119*50000000000000^1607 ≤ 17605158328271^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4531115021 10000000000 17605158328271 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4163203927/10000000000 : ℝ)^2119 ≤ (15745085681273/50000000000000 : ℝ)^1607 := by
    have hnat : (4163203927 : ℕ)^2119*50000000000000^1607 ≤ 15745085681273^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4163203927 10000000000 15745085681273 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4343382307/10000000000 : ℝ), (4531115021/10000000000 : ℝ), (4163203927/10000000000 : ℝ)] ![(3329951195971/10000000000000 : ℝ), (17605158328271/50000000000000 : ℝ), (15745085681273/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4343382307/10000000000 : ℝ)|^2119 ≤ (3329951195971/10000000000000 : ℝ)^1607
        have hw : |(4343382307/10000000000 : ℝ)|=(4343382307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4531115021/10000000000 : ℝ)|^2119 ≤ (17605158328271/50000000000000 : ℝ)^1607
        have hw : |(4531115021/10000000000 : ℝ)|=(4531115021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4163203927/10000000000 : ℝ)|^2119 ≤ (15745085681273/50000000000000 : ℝ)^1607
        have hw : |(4163203927/10000000000 : ℝ)|=(4163203927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1278_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152212411/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7543/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5297/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10911/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3687/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7543/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5297/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7543/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5297/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7543/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5297/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7543/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5297/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7543/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5297/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7543/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5297/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5297/50000 : ℝ) ^ (4237/1024 : ℝ) ≤ (4623439791682821/50000000000000000000 : ℝ) := by
    have hpowers : (5297/50000 : ℝ)^4237 ≤ (4623439791682821/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5297 : ℕ)^4237*50000000000000000000^1024 ≤ 4623439791682821^1024*50000^4237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5297 50000 4623439791682821 50000000000000000000 4237 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5297/50000 : ℝ)) (X := (4623439791682821/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7543/50000 : ℝ) ^ (4237/1024 : ℝ) ≤ (7983988700816329/20000000000000000000 : ℝ) := by
    have hpowers : (7543/50000 : ℝ)^4237 ≤ (7983988700816329/20000000000000000000 : ℝ)^1024 := by
      have hnat : (7543 : ℕ)^4237*20000000000000000000^1024 ≤ 7983988700816329^1024*50000^4237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7543 50000 7983988700816329 20000000000000000000 4237 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7543/50000 : ℝ)) (X := (7983988700816329/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004623439791682821/25000000000000000000 : ℝ) ≤ (2500111731659243/2500000000000000 : ℝ) ^ (4237/1024 : ℝ) := by
    have hpowers : (25004623439791682821/25000000000000000000 : ℝ)^1024 ≤ (2500111731659243/2500000000000000 : ℝ)^4237 := by
      have hnat : (25004623439791682821 : ℕ)^1024*2500000000000000^4237 ≤ 2500111731659243^4237*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004623439791682821 25000000000000000000 2500111731659243 2500000000000000 1024 4237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500111731659243/2500000000000000 : ℝ)) (X := (25004623439791682821/25000000000000000000 : ℝ)) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049166823087447287/100000000000000000000 : ℝ) ≤ (200023760889237/200000000000000 : ℝ) ^ (4237/1024 : ℝ) := by
    have hpowers : (100049166823087447287/100000000000000000000 : ℝ)^1024 ≤ (200023760889237/200000000000000 : ℝ)^4237 := by
      have hnat : (100049166823087447287 : ℕ)^1024*200000000000000^4237 ≤ 200023760889237^4237*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049166823087447287 100000000000000000000 200023760889237 200000000000000 1024 4237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200023760889237/200000000000000 : ℝ)) (X := (100049166823087447287/100000000000000000000 : ℝ)) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007983988700816329/10000000000000000000 : ℝ) ≤ (1250241145285841/1250000000000000 : ℝ) ^ (4237/1024 : ℝ) := by
    have hpowers : (10007983988700816329/10000000000000000000 : ℝ)^1024 ≤ (1250241145285841/1250000000000000 : ℝ)^4237 := by
      have hnat : (10007983988700816329 : ℕ)^1024*1250000000000000^4237 ≤ 1250241145285841^4237*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007983988700816329 10000000000000000000 1250241145285841 1250000000000000 1024 4237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250241145285841/1250000000000000 : ℝ)) (X := (10007983988700816329/10000000000000000000 : ℝ)) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4623439791682821/50000000000000000000 : ℝ) ≤ ((1122657619749494079/1123000000000000000 : ℝ)+2*(370558912439/224600000000000 : ℝ)*(5297/50000 : ℝ))^(4237/1024 : ℝ) := by
    rw [show (1122657619749494079/1123000000000000000 : ℝ)+2*(370558912439/224600000000000 : ℝ)*(5297/50000 : ℝ)=(2500111731659243/2500000000000000 : ℝ) by norm_num, show 1+2*(4623439791682821/50000000000000000000 : ℝ)=(25004623439791682821/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7983988700816329/20000000000000000000 : ℝ)+(4623439791682821/50000000000000000000 : ℝ) ≤ ((1122657619749494079/1123000000000000000 : ℝ)+(370558912439/224600000000000 : ℝ)*((7543/50000 : ℝ)+(5297/50000 : ℝ)))^(4237/1024 : ℝ) := by
    rw [show (1122657619749494079/1123000000000000000 : ℝ)+(370558912439/224600000000000 : ℝ)*((7543/50000 : ℝ)+(5297/50000 : ℝ))=(200023760889237/200000000000000 : ℝ) by norm_num, show 1+(7983988700816329/20000000000000000000 : ℝ)+(4623439791682821/50000000000000000000 : ℝ)=(100049166823087447287/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7983988700816329/20000000000000000000 : ℝ) ≤ ((1122657619749494079/1123000000000000000 : ℝ)+2*(370558912439/224600000000000 : ℝ)*(7543/50000 : ℝ))^(4237/1024 : ℝ) := by
    rw [show (1122657619749494079/1123000000000000000 : ℝ)+2*(370558912439/224600000000000 : ℝ)*(7543/50000 : ℝ)=(1250241145285841/1250000000000000 : ℝ) by norm_num, show 1+2*(7983988700816329/20000000000000000000 : ℝ)=(10007983988700816329/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1122657619749494079/1123000000000000000 : ℝ)*(X 1 0+X 2 0)+(370558912439/224600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4237/1024 : ℝ)) (lo := (5297/50000 : ℝ)) (hi := (7543/50000 : ℝ)) (c := (1122657619749494079/1123000000000000000 : ℝ)) (alpha := (370558912439/224600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1122657619749494079/1123000000000000000 : ℝ)*(X 0 1+X 2 1)+(370558912439/224600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4237/1024 : ℝ)) (lo := (5297/50000 : ℝ)) (hi := (7543/50000 : ℝ)) (c := (1122657619749494079/1123000000000000000 : ℝ)) (alpha := (370558912439/224600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1122657619749494079/1123000000000000000 : ℝ)*(X 0 2+X 1 2)+(370558912439/224600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4237/1024 : ℝ)) (lo := (5297/50000 : ℝ)) (hi := (7543/50000 : ℝ)) (c := (1122657619749494079/1123000000000000000 : ℝ)) (alpha := (370558912439/224600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2100099837/10000000000 : ℝ)*X 0 0+(2710017431/5000000000 : ℝ)*X 0 1+(5238707903/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337754349/2500000000 : ℝ)*X 1 0+(-1096312199/5000000000 : ℝ)*X 1 1+(5238707867/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351017089/10000000000 : ℝ)*X 2 0+(5238708133/10000000000 : ℝ)*X 2 1+(-438524891/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((108583801/250000000 : ℝ)*X 0 0+(2080908727/5000000000 : ℝ)*X 0 1+(453249431/1000000000 : ℝ)*X 0 2+(108583801/250000000 : ℝ)*X 1 0+(2080908727/5000000000 : ℝ)*X 1 1+(453249431/1000000000 : ℝ)*X 1 2+(108583801/250000000 : ℝ)*X 2 0+(2080908727/5000000000 : ℝ)*X 2 1+(453249431/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2100114959/10000000000 : ℝ)*X 0 0+(523938239/1000000000 : ℝ)*X 0 1+(5419356441/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304675849/10000000000 : ℝ)*X 1 0+(-2011975709/10000000000 : ℝ)*X 1 1+(5419356537/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652337887/5000000000 : ℝ)*X 2 0+(1354839101/2500000000 : ℝ)*X 2 1+(-2011975993/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4343382307/10000000000 : ℝ)*X 0 0+(4531115021/10000000000 : ℝ)*X 0 1+(4163203927/10000000000 : ℝ)*X 0 2+(4343382307/10000000000 : ℝ)*X 1 0+(4531115021/10000000000 : ℝ)*X 1 1+(4163203927/10000000000 : ℝ)*X 1 2+(4343382307/10000000000 : ℝ)*X 2 0+(4531115021/10000000000 : ℝ)*X 2 1+(4163203927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (123553656586878679412215899/14037500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (388251139/100000000000000 : ℝ)*(base19) + (88642881/50000000000000 : ℝ)*(base23) + (55549937/50000000000000 : ℝ)*(lower2) + (44066841/100000000000000 : ℝ)*(upper3) + (167519913/100000000000000 : ℝ)*(lower4) + (1026586462998009/25000000000000 : ℝ)*(major0) + (1026586462998009/25000000000000 : ℝ)*(major1) + (1026586462998009/25000000000000 : ℝ)*(major2) + (2757455685409101/50000000000000 : ℝ)*(sp0) + (689364709647217/12500000000000 : ℝ)*(sp1) + (5514917888143113/100000000000000 : ℝ)*(sp2) + (1348885450293151/50000000000000 : ℝ)*(sp3) + (6694610673/100000000000000 : ℝ)*(sp4) + (122228969/5000000000000 : ℝ)*(sp7) + (1348886672582841/50000000000000 : ℝ)*(f.failure) + (44119344523431/800000000000 : ℝ)*(f.sum) + (41266682711383/5615000000000000000000000000 : ℝ)*base66 + (224733179243106289/28075000000000000000000000000000 : ℝ)*base68 + (150130138613881289/28075000000000000000000000000000 : ℝ)*base70 + (362454881573656289/28075000000000000000000000000000 : ℝ)*base72 + (7457987342251/2807500000000000000000000000 : ℝ)*base73 + (229776215971356289/28075000000000000000000000000000 : ℝ)*base76 + (379882791596731289/28075000000000000000000000000000 : ℝ)*base78 + (168993956780731289/28075000000000000000000000000000 : ℝ)*base80 + (604691186927/5615000000000000000000000000 : ℝ)*base81 + (25839651/5000000000000000000000 : ℝ)*base89 + (25839651/5000000000000000000000 : ℝ)*base91 + (25839651/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (237812195781529788162375009/28075000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (224295553/20000000000000 : ℝ)*(base19) + (1155375261/100000000000000 : ℝ)*(base23) + (24037589/25000000000000 : ℝ)*(upper3) + (12789643/12500000000000 : ℝ)*(lower4) + (228546983/100000000000000 : ℝ)*(upper5) + (4137201494819943/100000000000000 : ℝ)*(major0) + (4137201494819943/100000000000000 : ℝ)*(major1) + (4137201494819943/100000000000000 : ℝ)*(major2) + (26067153467/100000000000000 : ℝ)*(sp1) + (421526003/2500000000000 : ℝ)*(sp2) + (5556357925235147/100000000000000 : ℝ)*(sp4) + (2778165368301957/50000000000000 : ℝ)*(sp5) + (1111267981763953/20000000000000 : ℝ)*(sp6) + (679511195512819/25000000000000 : ℝ)*(sp7) + (679511195512819/25000000000000 : ℝ)*(f.failure) + (5556357925235147/100000000000000 : ℝ)*(f.sum) + (17480518622593/11230000000000000000000000000 : ℝ)*base66 + (528070979754702497/112300000000000000000000000000000 : ℝ)*base67 + (468851444547197503/112300000000000000000000000000000 : ℝ)*base70 + (1008324116909502497/112300000000000000000000000000000 : ℝ)*base71 + (18166605870943/11230000000000000000000000000 : ℝ)*base74 + (1322234857228802497/112300000000000000000000000000000 : ℝ)*base75 + (135854313583902497/112300000000000000000000000000000 : ℝ)*base77 + (1514406406567702497/112300000000000000000000000000000 : ℝ)*base79 + (60475863365633/11230000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (13603391/2500000000000000000000 : ℝ)*base90 + (13603391/2500000000000000000000 : ℝ)*base92 + (13603391/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1278_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152212411/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7543/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5297/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10911/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1278_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1278_s5_0 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1050248263/5000000000 : ℝ)*x 0 + (1354172953/2500000000 : ℝ)*x 1 + (5241790301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050248263/5000000000 : ℝ)^2119 ≤ (1277643276257/10000000000000 : ℝ)^1607 := by
    have hnat : (1050248263 : ℕ)^2119*10000000000000^1607 ≤ 1277643276257^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050248263 5000000000 1277643276257 10000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1354172953/2500000000 : ℝ)^2119 ≤ (5569423060057/12500000000000 : ℝ)^1607 := by
    have hnat : (1354172953 : ℕ)^2119*12500000000000^1607 ≤ 5569423060057^1607*2500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354172953 2500000000 5569423060057 12500000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241790301/10000000000 : ℝ)^2119 ≤ (42668182741133/100000000000000 : ℝ)^1607 := by
    have hnat : (5241790301 : ℕ)^2119*100000000000000^1607 ≤ 42668182741133^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241790301 10000000000 42668182741133 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1050248263/5000000000 : ℝ), (1354172953/2500000000 : ℝ), (5241790301/10000000000 : ℝ)] ![(1277643276257/10000000000000 : ℝ), (5569423060057/12500000000000 : ℝ), (42668182741133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1050248263/5000000000 : ℝ)|^2119 ≤ (1277643276257/10000000000000 : ℝ)^1607
        have hw : |(-1050248263/5000000000 : ℝ)|=(1050248263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1354172953/2500000000 : ℝ)|^2119 ≤ (5569423060057/12500000000000 : ℝ)^1607
        have hw : |(1354172953/2500000000 : ℝ)|=(1354172953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241790301/10000000000 : ℝ)|^2119 ≤ (42668182741133/100000000000000 : ℝ)^1607
        have hw : |(5241790301/10000000000 : ℝ)|=(5241790301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s5_1 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1337542981/2500000000 : ℝ)*x 0 + (-437935703/2000000000 : ℝ)*x 1 + (655223789/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337542981/2500000000 : ℝ)^2119 ≤ (2739706626557/6250000000000 : ℝ)^1607 := by
    have hnat : (1337542981 : ℕ)^2119*6250000000000^1607 ≤ 2739706626557^1607*2500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337542981 2500000000 2739706626557 6250000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (437935703/2000000000 : ℝ)^2119 ≤ (2699302220713/20000000000000 : ℝ)^1607 := by
    have hnat : (437935703 : ℕ)^2119*20000000000000^1607 ≤ 2699302220713^1607*2000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437935703 2000000000 2699302220713 20000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655223789/1250000000 : ℝ)^2119 ≤ (42668182859201/100000000000000 : ℝ)^1607 := by
    have hnat : (655223789 : ℕ)^2119*100000000000000^1607 ≤ 42668182859201^1607*1250000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655223789 1250000000 42668182859201 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337542981/2500000000 : ℝ), (-437935703/2000000000 : ℝ), (655223789/1250000000 : ℝ)] ![(2739706626557/6250000000000 : ℝ), (2699302220713/20000000000000 : ℝ), (42668182859201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337542981/2500000000 : ℝ)|^2119 ≤ (2739706626557/6250000000000 : ℝ)^1607
        have hw : |(1337542981/2500000000 : ℝ)|=(1337542981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-437935703/2000000000 : ℝ)|^2119 ≤ (2699302220713/20000000000000 : ℝ)^1607
        have hw : |(-437935703/2000000000 : ℝ)|=(437935703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655223789/1250000000 : ℝ)|^2119 ≤ (42668182859201/100000000000000 : ℝ)^1607
        have hw : |(655223789/1250000000 : ℝ)|=(655223789/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s5_2 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5350171951/10000000000 : ℝ)*x 0 + (5241790321/10000000000 : ℝ)*x 1 + (-2189678467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350171951/10000000000 : ℝ)^2119 ≤ (43835306316611/100000000000000 : ℝ)^1607 := by
    have hnat : (5350171951 : ℕ)^2119*100000000000000^1607 ≤ 43835306316611^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350171951 10000000000 43835306316611 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241790321/10000000000 : ℝ)^2119 ≤ (21334091477901/50000000000000 : ℝ)^1607 := by
    have hnat : (5241790321 : ℕ)^2119*50000000000000^1607 ≤ 21334091477901^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241790321 10000000000 21334091477901 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2189678467/10000000000 : ℝ)^2119 ≤ (2699302142689/20000000000000 : ℝ)^1607 := by
    have hnat : (2189678467 : ℕ)^2119*20000000000000^1607 ≤ 2699302142689^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189678467 10000000000 2699302142689 20000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350171951/10000000000 : ℝ), (5241790321/10000000000 : ℝ), (-2189678467/10000000000 : ℝ)] ![(43835306316611/100000000000000 : ℝ), (21334091477901/50000000000000 : ℝ), (2699302142689/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350171951/10000000000 : ℝ)|^2119 ≤ (43835306316611/100000000000000 : ℝ)^1607
        have hw : |(5350171951/10000000000 : ℝ)|=(5350171951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241790321/10000000000 : ℝ)|^2119 ≤ (21334091477901/50000000000000 : ℝ)^1607
        have hw : |(5241790321/10000000000 : ℝ)|=(5241790321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2189678467/10000000000 : ℝ)|^2119 ≤ (2699302142689/20000000000000 : ℝ)^1607
        have hw : |(-2189678467/10000000000 : ℝ)|=(2189678467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s5_3 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2171793617/5000000000 : ℝ)*x 0 + (208417739/500000000 : ℝ)*x 1 + (2262948577/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171793617/5000000000 : ℝ)^2119 ≤ (33301583661957/100000000000000 : ℝ)^1607 := by
    have hnat : (2171793617 : ℕ)^2119*100000000000000^1607 ≤ 33301583661957^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171793617 5000000000 33301583661957 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208417739/500000000 : ℝ)^2119 ≤ (31541555271551/100000000000000 : ℝ)^1607 := by
    have hnat : (208417739 : ℕ)^2119*100000000000000^1607 ≤ 31541555271551^1607*500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208417739 500000000 31541555271551 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2262948577/5000000000 : ℝ)^2119 ≤ (35156861053827/100000000000000 : ℝ)^1607 := by
    have hnat : (2262948577 : ℕ)^2119*100000000000000^1607 ≤ 35156861053827^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262948577 5000000000 35156861053827 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2171793617/5000000000 : ℝ), (208417739/500000000 : ℝ), (2262948577/5000000000 : ℝ)] ![(33301583661957/100000000000000 : ℝ), (31541555271551/100000000000000 : ℝ), (35156861053827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2171793617/5000000000 : ℝ)|^2119 ≤ (33301583661957/100000000000000 : ℝ)^1607
        have hw : |(2171793617/5000000000 : ℝ)|=(2171793617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(208417739/500000000 : ℝ)|^2119 ≤ (31541555271551/100000000000000 : ℝ)^1607
        have hw : |(208417739/500000000 : ℝ)|=(208417739/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2262948577/5000000000 : ℝ)|^2119 ≤ (35156861053827/100000000000000 : ℝ)^1607
        have hw : |(2262948577/5000000000 : ℝ)|=(2262948577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s5_4 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-262563707/1250000000 : ℝ)*x 0 + (2621209109/5000000000 : ℝ)*x 1 + (2708030347/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262563707/1250000000 : ℝ)^2119 ≤ (255530761443/2000000000000 : ℝ)^1607 := by
    have hnat : (262563707 : ℕ)^2119*2000000000000^1607 ≤ 255530761443^1607*1250000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262563707 1250000000 255530761443 2000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621209109/5000000000 : ℝ)^2119 ≤ (10668730647321/25000000000000 : ℝ)^1607 := by
    have hnat : (2621209109 : ℕ)^2119*25000000000000^1607 ≤ 10668730647321^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621209109 5000000000 10668730647321 25000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2708030347/5000000000 : ℝ)^2119 ≤ (22274269659829/50000000000000 : ℝ)^1607 := by
    have hnat : (2708030347 : ℕ)^2119*50000000000000^1607 ≤ 22274269659829^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708030347 5000000000 22274269659829 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-262563707/1250000000 : ℝ), (2621209109/5000000000 : ℝ), (2708030347/5000000000 : ℝ)] ![(255530761443/2000000000000 : ℝ), (10668730647321/25000000000000 : ℝ), (22274269659829/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-262563707/1250000000 : ℝ)|^2119 ≤ (255530761443/2000000000000 : ℝ)^1607
        have hw : |(-262563707/1250000000 : ℝ)|=(262563707/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621209109/5000000000 : ℝ)|^2119 ≤ (10668730647321/25000000000000 : ℝ)^1607
        have hw : |(2621209109/5000000000 : ℝ)|=(2621209109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2708030347/5000000000 : ℝ)|^2119 ≤ (22274269659829/50000000000000 : ℝ)^1607
        have hw : |(2708030347/5000000000 : ℝ)|=(2708030347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s5_5 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2652736411/5000000000 : ℝ)*x 0 + (-2015408007/10000000000 : ℝ)*x 1 + (5416060843/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652736411/5000000000 : ℝ)^2119 ≤ (10838258885937/25000000000000 : ℝ)^1607 := by
    have hnat : (2652736411 : ℕ)^2119*25000000000000^1607 ≤ 10838258885937^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652736411 5000000000 10838258885937 25000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2015408007/10000000000 : ℝ)^2119 ≤ (120984235001/1000000000000 : ℝ)^1607 := by
    have hnat : (2015408007 : ℕ)^2119*1000000000000^1607 ≤ 120984235001^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015408007 10000000000 120984235001 1000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416060843/10000000000 : ℝ)^2119 ≤ (8909708187139/20000000000000 : ℝ)^1607 := by
    have hnat : (5416060843 : ℕ)^2119*20000000000000^1607 ≤ 8909708187139^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416060843 10000000000 8909708187139 20000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652736411/5000000000 : ℝ), (-2015408007/10000000000 : ℝ), (5416060843/10000000000 : ℝ)] ![(10838258885937/25000000000000 : ℝ), (120984235001/1000000000000 : ℝ), (8909708187139/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652736411/5000000000 : ℝ)|^2119 ≤ (10838258885937/25000000000000 : ℝ)^1607
        have hw : |(2652736411/5000000000 : ℝ)|=(2652736411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2015408007/10000000000 : ℝ)|^2119 ≤ (120984235001/1000000000000 : ℝ)^1607
        have hw : |(-2015408007/10000000000 : ℝ)|=(2015408007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416060843/10000000000 : ℝ)|^2119 ≤ (8909708187139/20000000000000 : ℝ)^1607
        have hw : |(5416060843/10000000000 : ℝ)|=(5416060843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s5_6 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326368159/2500000000 : ℝ)*x 0 + (541606109/1000000000 : ℝ)*x 1 + (-1007703961/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326368159/2500000000 : ℝ)^2119 ≤ (43353033539629/100000000000000 : ℝ)^1607 := by
    have hnat : (1326368159 : ℕ)^2119*100000000000000^1607 ≤ 43353033539629^1607*2500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326368159 2500000000 43353033539629 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541606109/1000000000 : ℝ)^2119 ≤ (44548543614629/100000000000000 : ℝ)^1607 := by
    have hnat : (541606109 : ℕ)^2119*100000000000000^1607 ≤ 44548543614629^1607*1000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541606109 1000000000 44548543614629 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1007703961/5000000000 : ℝ)^2119 ≤ (12098422827279/100000000000000 : ℝ)^1607 := by
    have hnat : (1007703961 : ℕ)^2119*100000000000000^1607 ≤ 12098422827279^1607*5000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007703961 5000000000 12098422827279 100000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326368159/2500000000 : ℝ), (541606109/1000000000 : ℝ), (-1007703961/5000000000 : ℝ)] ![(43353033539629/100000000000000 : ℝ), (44548543614629/100000000000000 : ℝ), (12098422827279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326368159/2500000000 : ℝ)|^2119 ≤ (43353033539629/100000000000000 : ℝ)^1607
        have hw : |(1326368159/2500000000 : ℝ)|=(1326368159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541606109/1000000000 : ℝ)|^2119 ≤ (44548543614629/100000000000000 : ℝ)^1607
        have hw : |(541606109/1000000000 : ℝ)|=(541606109/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1007703961/5000000000 : ℝ)|^2119 ≤ (12098422827279/100000000000000 : ℝ)^1607
        have hw : |(-1007703961/5000000000 : ℝ)|=(1007703961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1278_s5_7 (p : ℝ) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1085903487/2500000000 : ℝ)*x 0 + (4524613903/10000000000 : ℝ)*x 1 + (1042411233/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085903487/2500000000 : ℝ)^2119 ≤ (4162731716061/12500000000000 : ℝ)^1607 := by
    have hnat : (1085903487 : ℕ)^2119*12500000000000^1607 ≤ 4162731716061^1607*2500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085903487 2500000000 4162731716061 12500000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4524613903/10000000000 : ℝ)^2119 ≤ (17571858754887/50000000000000 : ℝ)^1607 := by
    have hnat : (4524613903 : ℕ)^2119*50000000000000^1607 ≤ 17571858754887^1607*10000000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524613903 10000000000 17571858754887 50000000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1042411233/2500000000 : ℝ)^2119 ≤ (3944303593339/12500000000000 : ℝ)^1607 := by
    have hnat : (1042411233 : ℕ)^2119*12500000000000^1607 ≤ 3944303593339^1607*2500000000^2119 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042411233 2500000000 3944303593339 12500000000000 2119 1607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2119/512 : ℝ)) 2119 1607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1085903487/2500000000 : ℝ), (4524613903/10000000000 : ℝ), (1042411233/2500000000 : ℝ)] ![(4162731716061/12500000000000 : ℝ), (17571858754887/50000000000000 : ℝ), (3944303593339/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1085903487/2500000000 : ℝ)|^2119 ≤ (4162731716061/12500000000000 : ℝ)^1607
        have hw : |(1085903487/2500000000 : ℝ)|=(1085903487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4524613903/10000000000 : ℝ)|^2119 ≤ (17571858754887/50000000000000 : ℝ)^1607
        have hw : |(4524613903/10000000000 : ℝ)|=(4524613903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1042411233/2500000000 : ℝ)|^2119 ≤ (3944303593339/12500000000000 : ℝ)^1607
        have hw : |(1042411233/2500000000 : ℝ)|=(1042411233/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1278_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152212411/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10911/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10977/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7339/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3687/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10911/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3687/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10911/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3687/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10911/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3687/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10911/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3687/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10911/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3687/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10911/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10911/100000 : ℝ) ^ (4237/1024 : ℝ) ≤ (10446641289961999/100000000000000000000 : ℝ) := by
    have hpowers : (10911/100000 : ℝ)^4237 ≤ (10446641289961999/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10911 : ℕ)^4237*100000000000000000000^1024 ≤ 10446641289961999^1024*100000^4237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10911 100000 10446641289961999 100000000000000000000 4237 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10911/100000 : ℝ)) (X := (10446641289961999/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3687/25000 : ℝ) ^ (4237/1024 : ℝ) ≤ (9086800072551/25000000000000000 : ℝ) := by
    have hpowers : (3687/25000 : ℝ)^4237 ≤ (9086800072551/25000000000000000 : ℝ)^1024 := by
      have hnat : (3687 : ℕ)^4237*25000000000000000^1024 ≤ 9086800072551^1024*25000^4237 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3687 25000 9086800072551 25000000000000000 4237 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3687/25000 : ℝ)) (X := (9086800072551/25000000000000000 : ℝ)) (by norm_num) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010446641289961999/50000000000000000000 : ℝ) ≤ (2500126227441011/2500000000000000 : ℝ) ^ (4237/1024 : ℝ) := by
    have hpowers : (50010446641289961999/50000000000000000000 : ℝ)^1024 ≤ (2500126227441011/2500000000000000 : ℝ)^4237 := by
      have hnat : (50010446641289961999 : ℕ)^1024*2500000000000000^4237 ≤ 2500126227441011^4237*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010446641289961999 50000000000000000000 2500126227441011 2500000000000000 1024 4237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500126227441011/2500000000000000 : ℝ)) (X := (50010446641289961999/50000000000000000000 : ℝ)) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046793841580165999/100000000000000000000 : ℝ) ≤ (2000226142999903/2000000000000000 : ℝ) ^ (4237/1024 : ℝ) := by
    have hpowers : (100046793841580165999/100000000000000000000 : ℝ)^1024 ≤ (2000226142999903/2000000000000000 : ℝ)^4237 := by
      have hnat : (100046793841580165999 : ℕ)^1024*2000000000000000^4237 ≤ 2000226142999903^4237*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046793841580165999 100000000000000000000 2000226142999903 2000000000000000 1024 4237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000226142999903/2000000000000000 : ℝ)) (X := (100046793841580165999/100000000000000000000 : ℝ)) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509086800072551/12500000000000000 : ℝ) ≤ (5000878260117493/5000000000000000 : ℝ) ^ (4237/1024 : ℝ) := by
    have hpowers : (12509086800072551/12500000000000000 : ℝ)^1024 ≤ (5000878260117493/5000000000000000 : ℝ)^4237 := by
      have hnat : (12509086800072551 : ℕ)^1024*5000000000000000^4237 ≤ 5000878260117493^4237*12500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509086800072551 12500000000000000 5000878260117493 5000000000000000 1024 4237 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000878260117493/5000000000000000 : ℝ)) (X := (12509086800072551/12500000000000000 : ℝ)) (by norm_num) 4237 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10446641289961999/100000000000000000000 : ℝ) ≤ ((6393046836152698111/6395000000000000000 : ℝ)+2*(208601745157/127900000000000 : ℝ)*(10911/100000 : ℝ))^(4237/1024 : ℝ) := by
    rw [show (6393046836152698111/6395000000000000000 : ℝ)+2*(208601745157/127900000000000 : ℝ)*(10911/100000 : ℝ)=(2500126227441011/2500000000000000 : ℝ) by norm_num, show 1+2*(10446641289961999/100000000000000000000 : ℝ)=(50010446641289961999/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9086800072551/25000000000000000 : ℝ)+(10446641289961999/100000000000000000000 : ℝ) ≤ ((6393046836152698111/6395000000000000000 : ℝ)+(208601745157/127900000000000 : ℝ)*((3687/25000 : ℝ)+(10911/100000 : ℝ)))^(4237/1024 : ℝ) := by
    rw [show (6393046836152698111/6395000000000000000 : ℝ)+(208601745157/127900000000000 : ℝ)*((3687/25000 : ℝ)+(10911/100000 : ℝ))=(2000226142999903/2000000000000000 : ℝ) by norm_num, show 1+(9086800072551/25000000000000000 : ℝ)+(10446641289961999/100000000000000000000 : ℝ)=(100046793841580165999/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9086800072551/25000000000000000 : ℝ) ≤ ((6393046836152698111/6395000000000000000 : ℝ)+2*(208601745157/127900000000000 : ℝ)*(3687/25000 : ℝ))^(4237/1024 : ℝ) := by
    rw [show (6393046836152698111/6395000000000000000 : ℝ)+2*(208601745157/127900000000000 : ℝ)*(3687/25000 : ℝ)=(5000878260117493/5000000000000000 : ℝ) by norm_num, show 1+2*(9086800072551/25000000000000000 : ℝ)=(12509086800072551/12500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6393046836152698111/6395000000000000000 : ℝ)*(X 1 0+X 2 0)+(208601745157/127900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4237/1024 : ℝ)) (lo := (10911/100000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (6393046836152698111/6395000000000000000 : ℝ)) (alpha := (208601745157/127900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6393046836152698111/6395000000000000000 : ℝ)*(X 0 1+X 2 1)+(208601745157/127900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4237/1024 : ℝ)) (lo := (10911/100000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (6393046836152698111/6395000000000000000 : ℝ)) (alpha := (208601745157/127900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6393046836152698111/6395000000000000000 : ℝ)*(X 0 2+X 1 2)+(208601745157/127900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4237/1024 : ℝ)) (lo := (10911/100000 : ℝ)) (hi := (3687/25000 : ℝ)) (c := (6393046836152698111/6395000000000000000 : ℝ)) (alpha := (208601745157/127900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1050248263/5000000000 : ℝ)*X 0 0+(1354172953/2500000000 : ℝ)*X 0 1+(5241790301/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337542981/2500000000 : ℝ)*X 1 0+(-437935703/2000000000 : ℝ)*X 1 1+(655223789/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350171951/10000000000 : ℝ)*X 2 0+(5241790321/10000000000 : ℝ)*X 2 1+(-2189678467/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2171793617/5000000000 : ℝ)*X 0 0+(208417739/500000000 : ℝ)*X 0 1+(2262948577/5000000000 : ℝ)*X 0 2+(2171793617/5000000000 : ℝ)*X 1 0+(208417739/500000000 : ℝ)*X 1 1+(2262948577/5000000000 : ℝ)*X 1 2+(2171793617/5000000000 : ℝ)*X 2 0+(208417739/500000000 : ℝ)*X 2 1+(2262948577/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-262563707/1250000000 : ℝ)*X 0 0+(2621209109/5000000000 : ℝ)*X 0 1+(2708030347/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652736411/5000000000 : ℝ)*X 1 0+(-2015408007/10000000000 : ℝ)*X 1 1+(5416060843/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326368159/2500000000 : ℝ)*X 2 0+(541606109/1000000000 : ℝ)*X 2 1+(-1007703961/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1085903487/2500000000 : ℝ)*X 0 0+(4524613903/10000000000 : ℝ)*X 0 1+(1042411233/2500000000 : ℝ)*X 0 2+(1085903487/2500000000 : ℝ)*X 1 0+(4524613903/10000000000 : ℝ)*X 1 1+(1042411233/2500000000 : ℝ)*X 1 2+(1085903487/2500000000 : ℝ)*X 2 0+(4524613903/10000000000 : ℝ)*X 2 1+(1042411233/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1278_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (290534658475605038567044551/79937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50612987/6250000000000 : ℝ)*(base19) + (784795309/100000000000000 : ℝ)*(base23) + (7204861/25000000000000 : ℝ)*(lower2) + (30511751/25000000000000 : ℝ)*(upper3) + (143578497/100000000000000 : ℝ)*(upper5) + (1064302572490051/25000000000000 : ℝ)*(major0) + (1064302572490051/25000000000000 : ℝ)*(major1) + (1064302572490051/25000000000000 : ℝ)*(major2) + (1143503446432261/20000000000000 : ℝ)*(sp0) + (5717531890604087/100000000000000 : ℝ)*(sp1) + (571753191561657/10000000000000 : ℝ)*(sp2) + (1398439743601163/50000000000000 : ℝ)*(sp3) + (7734125287/50000000000000 : ℝ)*(sp4) + (1654231087/20000000000000 : ℝ)*(sp7) + (1398443879178881/50000000000000 : ℝ)*(f.failure) + (5717532700411879/100000000000000 : ℝ)*(f.sum) + (1493323030261/3197500000000000000000000000 : ℝ)*base66 + (634200234043968661/159875000000000000000000000000000 : ℝ)*base67 + (1224761871752468661/159875000000000000000000000000000 : ℝ)*base69 + (1932218296565843661/159875000000000000000000000000000 : ℝ)*base71 + (6580256910357/1598750000000000000000000000 : ℝ)*base73 + (2109931554970343661/159875000000000000000000000000000 : ℝ)*base75 + (970126569281093661/159875000000000000000000000000000 : ℝ)*base77 + (1946785626461218661/159875000000000000000000000000000 : ℝ)*base79 + (32885740545799/3197500000000000000000000000 : ℝ)*base81 + (22707909/5000000000000000000000 : ℝ)*base90 + (22707909/5000000000000000000000 : ℝ)*base92 + (22707909/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2165974591374458575250937939/319750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (915606083/100000000000000 : ℝ)*(base19) + (803185131/100000000000000 : ℝ)*(base23) + (27636801/12500000000000 : ℝ)*(upper3) + (15051727/100000000000000 : ℝ)*(lower4) + (59892057/100000000000000 : ℝ)*(upper5) + (4288050968875183/100000000000000 : ℝ)*(major0) + (4288050968875183/100000000000000 : ℝ)*(major1) + (4288050968875183/100000000000000 : ℝ)*(major2) + (16320730601/100000000000000 : ℝ)*(sp1) + (23573592097/100000000000000 : ℝ)*(sp2) + (5758952347649643/100000000000000 : ℝ)*(sp4) + (17996672222853/312500000000 : ℝ)*(sp5) + (1151785594174483/20000000000000 : ℝ)*(sp6) + (1408574682150979/50000000000000 : ℝ)*(sp7) + (1408574682150979/50000000000000 : ℝ)*(f.failure) + (5758952347649643/100000000000000 : ℝ)*(f.sum) + (27383529180789/6395000000000000000000000000 : ℝ)*base66 + (1086980884420570687/639500000000000000000000000000000 : ℝ)*base68 + (3140409532995570687/639500000000000000000000000000000 : ℝ)*base70 + (1072091738069429313/639500000000000000000000000000000 : ℝ)*base71 + (2131842869163/3197500000000000000000000000 : ℝ)*base73 + (11660295719720570687/639500000000000000000000000000000 : ℝ)*base76 + (1161501676420929313/639500000000000000000000000000000 : ℝ)*base77 + (5914009580084070687/639500000000000000000000000000000 : ℝ)*base80 + (19388982322217/3197500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (29600369/5000000000000000000000 : ℝ)*base89 + (29600369/5000000000000000000000 : ℝ)*base91 + (29600369/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1278_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152212411/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3687/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10911/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10977/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7339/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1278_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1278_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152212411/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16383/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (47/500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10977/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7339/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1278_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1278_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1278_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4237/1024 : ℝ) ≤ p) (hpb : p ≤ (2119/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152212411/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16383/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (47/500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10977/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7339/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1278_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
