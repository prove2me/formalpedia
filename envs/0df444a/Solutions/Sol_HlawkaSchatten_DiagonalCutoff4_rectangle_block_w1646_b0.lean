-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1646_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:11:57.750081+00:00
-- url     : https://prove2.me/submissions/5de85df4-59e2-40a0-ac0a-7258851f1d00

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
theorem support_rectangle_w1646_s0_0 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1499701727/10000000000 : ℝ)*x 0 + (1447568509/2500000000 : ℝ)*x 1 + (2459415111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1499701727/10000000000 : ℝ)^4903 ≤ (9088287952833/100000000000000 : ℝ)^3879 := by
    have hnat : (1499701727 : ℕ)^4903*100000000000000^3879 ≤ 9088287952833^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1499701727 10000000000 9088287952833 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1447568509/2500000000 : ℝ)^4903 ≤ (50125083726671/100000000000000 : ℝ)^3879 := by
    have hnat : (1447568509 : ℕ)^4903*100000000000000^3879 ≤ 50125083726671^3879*2500000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1447568509 2500000000 50125083726671 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2459415111/5000000000 : ℝ)^4903 ≤ (20393314150873/50000000000000 : ℝ)^3879 := by
    have hnat : (2459415111 : ℕ)^4903*50000000000000^3879 ≤ 20393314150873^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2459415111 5000000000 20393314150873 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1499701727/10000000000 : ℝ), (1447568509/2500000000 : ℝ), (2459415111/5000000000 : ℝ)] ![(9088287952833/100000000000000 : ℝ), (50125083726671/100000000000000 : ℝ), (20393314150873/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1499701727/10000000000 : ℝ)|^4903 ≤ (9088287952833/100000000000000 : ℝ)^3879
        have hw : |(-1499701727/10000000000 : ℝ)|=(1499701727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1447568509/2500000000 : ℝ)|^4903 ≤ (50125083726671/100000000000000 : ℝ)^3879
        have hw : |(1447568509/2500000000 : ℝ)|=(1447568509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2459415111/5000000000 : ℝ)|^4903 ≤ (20393314150873/50000000000000 : ℝ)^3879
        have hw : |(2459415111/5000000000 : ℝ)|=(2459415111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s0_1 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (169972647/312500000 : ℝ)*x 0 + (-1978458777/10000000000 : ℝ)*x 1 + (2459415583/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (169972647/312500000 : ℝ)^4903 ≤ (46314021661101/100000000000000 : ℝ)^3879 := by
    have hnat : (169972647 : ℕ)^4903*100000000000000^3879 ≤ 46314021661101^3879*312500000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169972647 312500000 46314021661101 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1978458777/10000000000 : ℝ)^4903 ≤ (12899340119029/100000000000000 : ℝ)^3879 := by
    have hnat : (1978458777 : ℕ)^4903*100000000000000^3879 ≤ 12899340119029^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1978458777 10000000000 12899340119029 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2459415583/5000000000 : ℝ)^4903 ≤ (8157327639141/20000000000000 : ℝ)^3879 := by
    have hnat : (2459415583 : ℕ)^4903*20000000000000^3879 ≤ 8157327639141^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2459415583 5000000000 8157327639141 20000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(169972647/312500000 : ℝ), (-1978458777/10000000000 : ℝ), (2459415583/5000000000 : ℝ)] ![(46314021661101/100000000000000 : ℝ), (12899340119029/100000000000000 : ℝ), (8157327639141/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(169972647/312500000 : ℝ)|^4903 ≤ (46314021661101/100000000000000 : ℝ)^3879
        have hw : |(169972647/312500000 : ℝ)|=(169972647/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1978458777/10000000000 : ℝ)|^4903 ≤ (12899340119029/100000000000000 : ℝ)^3879
        have hw : |(-1978458777/10000000000 : ℝ)|=(1978458777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2459415583/5000000000 : ℝ)|^4903 ≤ (8157327639141/20000000000000 : ℝ)^3879
        have hw : |(2459415583/5000000000 : ℝ)|=(2459415583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s0_2 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (339945433/625000000 : ℝ)*x 0 + (15371343/31250000 : ℝ)*x 1 + (-989228831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (339945433/625000000 : ℝ)^4903 ≤ (46314045597587/100000000000000 : ℝ)^3879 := by
    have hnat : (339945433 : ℕ)^4903*100000000000000^3879 ≤ 46314045597587^3879*625000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339945433 625000000 46314045597587 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15371343/31250000 : ℝ)^4903 ≤ (5098327932447/12500000000000 : ℝ)^3879 := by
    have hnat : (15371343 : ℕ)^4903*12500000000000^3879 ≤ 5098327932447^3879*31250000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15371343 31250000 5098327932447 12500000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (989228831/5000000000 : ℝ)^4903 ≤ (6449665465129/50000000000000 : ℝ)^3879 := by
    have hnat : (989228831 : ℕ)^4903*50000000000000^3879 ≤ 6449665465129^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989228831 5000000000 6449665465129 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(339945433/625000000 : ℝ), (15371343/31250000 : ℝ), (-989228831/5000000000 : ℝ)] ![(46314045597587/100000000000000 : ℝ), (5098327932447/12500000000000 : ℝ), (6449665465129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(339945433/625000000 : ℝ)|^4903 ≤ (46314045597587/100000000000000 : ℝ)^3879
        have hw : |(339945433/625000000 : ℝ)|=(339945433/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(15371343/31250000 : ℝ)|^4903 ≤ (5098327932447/12500000000000 : ℝ)^3879
        have hw : |(15371343/31250000 : ℝ)|=(15371343/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-989228831/5000000000 : ℝ)|^4903 ≤ (6449665465129/50000000000000 : ℝ)^3879
        have hw : |(-989228831/5000000000 : ℝ)|=(989228831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s0_3 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2046244469/5000000000 : ℝ)*x 0 + (3081633733/10000000000 : ℝ)*x 1 + (5324914781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2046244469/5000000000 : ℝ)^4903 ≤ (8081608877419/25000000000000 : ℝ)^3879 := by
    have hnat : (2046244469 : ℕ)^4903*25000000000000^3879 ≤ 8081608877419^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046244469 5000000000 8081608877419 25000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3081633733/10000000000 : ℝ)^4903 ≤ (564633442921/2500000000000 : ℝ)^3879 := by
    have hnat : (3081633733 : ℕ)^4903*2500000000000^3879 ≤ 564633442921^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3081633733 10000000000 564633442921 2500000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5324914781/10000000000 : ℝ)^4903 ≤ (5636028345541/12500000000000 : ℝ)^3879 := by
    have hnat : (5324914781 : ℕ)^4903*12500000000000^3879 ≤ 5636028345541^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5324914781 10000000000 5636028345541 12500000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2046244469/5000000000 : ℝ), (3081633733/10000000000 : ℝ), (5324914781/10000000000 : ℝ)] ![(8081608877419/25000000000000 : ℝ), (564633442921/2500000000000 : ℝ), (5636028345541/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2046244469/5000000000 : ℝ)|^4903 ≤ (8081608877419/25000000000000 : ℝ)^3879
        have hw : |(2046244469/5000000000 : ℝ)|=(2046244469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3081633733/10000000000 : ℝ)|^4903 ≤ (564633442921/2500000000000 : ℝ)^3879
        have hw : |(3081633733/10000000000 : ℝ)|=(3081633733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5324914781/10000000000 : ℝ)|^4903 ≤ (5636028345541/12500000000000 : ℝ)^3879
        have hw : |(5324914781/10000000000 : ℝ)|=(5324914781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s0_4 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1502043551/10000000000 : ℝ)*x 0 + (2470247127/5000000000 : ℝ)*x 1 + (5767859809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1502043551/10000000000 : ℝ)^4903 ≤ (2276557407339/25000000000000 : ℝ)^3879 := by
    have hnat : (1502043551 : ℕ)^4903*25000000000000^3879 ≤ 2276557407339^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1502043551 10000000000 2276557407339 25000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2470247127/5000000000 : ℝ)^4903 ≤ (20506909226393/50000000000000 : ℝ)^3879 := by
    have hnat : (2470247127 : ℕ)^4903*50000000000000^3879 ≤ 20506909226393^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2470247127 5000000000 20506909226393 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5767859809/10000000000 : ℝ)^4903 ≤ (24939975949369/50000000000000 : ℝ)^3879 := by
    have hnat : (5767859809 : ℕ)^4903*50000000000000^3879 ≤ 24939975949369^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5767859809 10000000000 24939975949369 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1502043551/10000000000 : ℝ), (2470247127/5000000000 : ℝ), (5767859809/10000000000 : ℝ)] ![(2276557407339/25000000000000 : ℝ), (20506909226393/50000000000000 : ℝ), (24939975949369/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1502043551/10000000000 : ℝ)|^4903 ≤ (2276557407339/25000000000000 : ℝ)^3879
        have hw : |(-1502043551/10000000000 : ℝ)|=(1502043551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2470247127/5000000000 : ℝ)|^4903 ≤ (20506909226393/50000000000000 : ℝ)^3879
        have hw : |(2470247127/5000000000 : ℝ)|=(2470247127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5767859809/10000000000 : ℝ)|^4903 ≤ (24939975949369/50000000000000 : ℝ)^3879
        have hw : |(5767859809/10000000000 : ℝ)|=(5767859809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s0_5 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (650162197/1250000000 : ℝ)*x 0 + (-564714159/5000000000 : ℝ)*x 1 + (5767859811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (650162197/1250000000 : ℝ)^4903 ≤ (10942317134447/25000000000000 : ℝ)^3879 := by
    have hnat : (650162197 : ℕ)^4903*25000000000000^3879 ≤ 10942317134447^3879*1250000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650162197 1250000000 10942317134447 25000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (564714159/5000000000 : ℝ)^4903 ≤ (6350779521451/100000000000000 : ℝ)^3879 := by
    have hnat : (564714159 : ℕ)^4903*100000000000000^3879 ≤ 6350779521451^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564714159 5000000000 6350779521451 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5767859811/10000000000 : ℝ)^4903 ≤ (49879951920599/100000000000000 : ℝ)^3879 := by
    have hnat : (5767859811 : ℕ)^4903*100000000000000^3879 ≤ 49879951920599^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5767859811 10000000000 49879951920599 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(650162197/1250000000 : ℝ), (-564714159/5000000000 : ℝ), (5767859811/10000000000 : ℝ)] ![(10942317134447/25000000000000 : ℝ), (6350779521451/100000000000000 : ℝ), (49879951920599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(650162197/1250000000 : ℝ)|^4903 ≤ (10942317134447/25000000000000 : ℝ)^3879
        have hw : |(650162197/1250000000 : ℝ)|=(650162197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-564714159/5000000000 : ℝ)|^4903 ≤ (6350779521451/100000000000000 : ℝ)^3879
        have hw : |(-564714159/5000000000 : ℝ)|=(564714159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5767859811/10000000000 : ℝ)|^4903 ≤ (49879951920599/100000000000000 : ℝ)^3879
        have hw : |(5767859811/10000000000 : ℝ)|=(5767859811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s0_6 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1300324421/2500000000 : ℝ)*x 0 + (57678597/100000000 : ℝ)*x 1 + (-564714163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1300324421/2500000000 : ℝ)^4903 ≤ (10942317421633/25000000000000 : ℝ)^3879 := by
    have hnat : (1300324421 : ℕ)^4903*25000000000000^3879 ≤ 10942317421633^3879*2500000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300324421 2500000000 10942317421633 25000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (57678597/100000000 : ℝ)^4903 ≤ (49879950707277/100000000000000 : ℝ)^3879 := by
    have hnat : (57678597 : ℕ)^4903*100000000000000^3879 ≤ 49879950707277^3879*100000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57678597 100000000 49879950707277 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (564714163/5000000000 : ℝ)^4903 ≤ (635077957831/10000000000000 : ℝ)^3879 := by
    have hnat : (564714163 : ℕ)^4903*10000000000000^3879 ≤ 635077957831^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564714163 5000000000 635077957831 10000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1300324421/2500000000 : ℝ), (57678597/100000000 : ℝ), (-564714163/5000000000 : ℝ)] ![(10942317421633/25000000000000 : ℝ), (49879950707277/100000000000000 : ℝ), (635077957831/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1300324421/2500000000 : ℝ)|^4903 ≤ (10942317421633/25000000000000 : ℝ)^3879
        have hw : |(1300324421/2500000000 : ℝ)|=(1300324421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(57678597/100000000 : ℝ)|^4903 ≤ (49879950707277/100000000000000 : ℝ)^3879
        have hw : |(57678597/100000000 : ℝ)|=(57678597/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-564714163/5000000000 : ℝ)|^4903 ≤ (635077957831/10000000000000 : ℝ)^3879
        have hw : |(-564714163/5000000000 : ℝ)|=(564714163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s0_7 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4098521403/10000000000 : ℝ)*x 0 + (1053829599/2000000000 : ℝ)*x 1 + (627865707/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4098521403/10000000000 : ℝ)^4903 ≤ (32386676442493/100000000000000 : ℝ)^3879 := by
    have hnat : (4098521403 : ℕ)^4903*100000000000000^3879 ≤ 32386676442493^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4098521403 10000000000 32386676442493 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053829599/2000000000 : ℝ)^4903 ≤ (22246099894431/50000000000000 : ℝ)^3879 := by
    have hnat : (1053829599 : ℕ)^4903*50000000000000^3879 ≤ 22246099894431^3879*2000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053829599 2000000000 22246099894431 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (627865707/2000000000 : ℝ)^4903 ≤ (23121123754649/100000000000000 : ℝ)^3879 := by
    have hnat : (627865707 : ℕ)^4903*100000000000000^3879 ≤ 23121123754649^3879*2000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627865707 2000000000 23121123754649 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4098521403/10000000000 : ℝ), (1053829599/2000000000 : ℝ), (627865707/2000000000 : ℝ)] ![(32386676442493/100000000000000 : ℝ), (22246099894431/50000000000000 : ℝ), (23121123754649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4098521403/10000000000 : ℝ)|^4903 ≤ (32386676442493/100000000000000 : ℝ)^3879
        have hw : |(4098521403/10000000000 : ℝ)|=(4098521403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053829599/2000000000 : ℝ)|^4903 ≤ (22246099894431/50000000000000 : ℝ)^3879
        have hw : |(1053829599/2000000000 : ℝ)|=(1053829599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(627865707/2000000000 : ℝ)|^4903 ≤ (23121123754649/100000000000000 : ℝ)^3879
        have hw : |(627865707/2000000000 : ℝ)|=(627865707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1646_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11169431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2383/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (11721/50000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (4899/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4899 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4899*1^1024 ≤ 0^1024*1^4899 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4899 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4899/1024 : ℝ) ≤ (1247910657335603487/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4899 ≤ (1247910657335603487/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4899*100000000000000000000^1024 ≤ 1247910657335603487^1024*5^4899 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1247910657335603487 100000000000000000000 4899 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1247910657335603487/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4899/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4899 := by
      have hnat : (1 : ℕ)^1024*1^4899 ≤ 1^4899*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4899 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101247910657335603487/100000000000000000000 : ℝ) ≤ (10025956325905989/10000000000000000 : ℝ) ^ (4899/1024 : ℝ) := by
    have hpowers : (101247910657335603487/100000000000000000000 : ℝ)^1024 ≤ (10025956325905989/10000000000000000 : ℝ)^4899 := by
      have hnat : (101247910657335603487 : ℕ)^1024*10000000000000000^4899 ≤ 10025956325905989^4899*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101247910657335603487 100000000000000000000 10025956325905989 10000000000000000 1024 4899 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10025956325905989/10000000000000000 : ℝ)) (X := (101247910657335603487/100000000000000000000 : ℝ)) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51247910657335603487/50000000000000000000 : ℝ) ≤ (5025956325905989/5000000000000000 : ℝ) ^ (4899/1024 : ℝ) := by
    have hpowers : (51247910657335603487/50000000000000000000 : ℝ)^1024 ≤ (5025956325905989/5000000000000000 : ℝ)^4899 := by
      have hnat : (51247910657335603487 : ℕ)^1024*5000000000000000^4899 ≤ 5025956325905989^4899*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51247910657335603487 50000000000000000000 5025956325905989 5000000000000000 1024 4899 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5025956325905989/5000000000000000 : ℝ)) (X := (51247910657335603487/50000000000000000000 : ℝ)) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(25956325905989/4000000000000000 : ℝ)*(0 : ℝ))^(4899/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(25956325905989/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1247910657335603487/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(25956325905989/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4899/1024 : ℝ) := by
    rw [show (1 : ℝ)+(25956325905989/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10025956325905989/10000000000000000 : ℝ) by norm_num, show 1+(1247910657335603487/100000000000000000000 : ℝ)+(0 : ℝ)=(101247910657335603487/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1247910657335603487/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(25956325905989/4000000000000000 : ℝ)*(2/5 : ℝ))^(4899/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(25956325905989/4000000000000000 : ℝ)*(2/5 : ℝ)=(5025956325905989/5000000000000000 : ℝ) by norm_num, show 1+2*(1247910657335603487/100000000000000000000 : ℝ)=(51247910657335603487/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(25956325905989/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4899/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (25956325905989/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(25956325905989/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4899/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (25956325905989/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(25956325905989/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4899/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (25956325905989/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1499701727/10000000000 : ℝ)*X 0 0+(1447568509/2500000000 : ℝ)*X 0 1+(2459415111/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((169972647/312500000 : ℝ)*X 1 0+(-1978458777/10000000000 : ℝ)*X 1 1+(2459415583/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((339945433/625000000 : ℝ)*X 2 0+(15371343/31250000 : ℝ)*X 2 1+(-989228831/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2046244469/5000000000 : ℝ)*X 0 0+(3081633733/10000000000 : ℝ)*X 0 1+(5324914781/10000000000 : ℝ)*X 0 2+(2046244469/5000000000 : ℝ)*X 1 0+(3081633733/10000000000 : ℝ)*X 1 1+(5324914781/10000000000 : ℝ)*X 1 2+(2046244469/5000000000 : ℝ)*X 2 0+(3081633733/10000000000 : ℝ)*X 2 1+(5324914781/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1502043551/10000000000 : ℝ)*X 0 0+(2470247127/5000000000 : ℝ)*X 0 1+(5767859809/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((650162197/1250000000 : ℝ)*X 1 0+(-564714159/5000000000 : ℝ)*X 1 1+(5767859811/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1300324421/2500000000 : ℝ)*X 2 0+(57678597/100000000 : ℝ)*X 2 1+(-564714163/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4098521403/10000000000 : ℝ)*X 0 0+(1053829599/2000000000 : ℝ)*X 0 1+(627865707/2000000000 : ℝ)*X 0 2+(4098521403/10000000000 : ℝ)*X 1 0+(1053829599/2000000000 : ℝ)*X 1 1+(627865707/2000000000 : ℝ)*X 1 2+(4098521403/10000000000 : ℝ)*X 2 0+(1053829599/2000000000 : ℝ)*X 2 1+(627865707/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (710096155052686239507543/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (223397851/25000000000000 : ℝ)*(base19) + (1090192481/100000000000000 : ℝ)*(base23) + (1385773/25000000000000 : ℝ)*(base24) + (36315429/25000000000000 : ℝ)*(upper4) + (130276387/50000000000000 : ℝ)*(upper5) + (796654287490471/100000000000000 : ℝ)*(major0) + (796654287490471/100000000000000 : ℝ)*(major1) + (796654287490471/100000000000000 : ℝ)*(major2) + (573761737095967/50000000000000 : ℝ)*(sp0) + (286882301086889/25000000000000 : ℝ)*(sp1) + (286882250550847/25000000000000 : ℝ)*(sp2) + (6965267509757/1562500000000 : ℝ)*(sp3) + (6623747027/100000000000000 : ℝ)*(sp4) + (1119718811/100000000000000 : ℝ)*(sp7) + (445778240343259/100000000000000 : ℝ)*(f.failure) + (1147530097938961/100000000000000 : ℝ)*(f.sum) + (399443246930819/200000000000000000000000000000 : ℝ)*base65 + (5089554930819/400000000000000000000000000000 : ℝ)*base67 + (2542293706269181/400000000000000000000000000000 : ℝ)*base70 + (777271686930819/400000000000000000000000000000 : ℝ)*base71 + (481140415930819/200000000000000000000000000000 : ℝ)*base73 + (1400038948269181/400000000000000000000000000000 : ℝ)*base76 + (407531769069181/400000000000000000000000000000 : ℝ)*base78 + (836237804269181/400000000000000000000000000000 : ℝ)*base80 + (164392495930819/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (3965629/625000000000000000000 : ℝ)*base89 + (3965629/625000000000000000000 : ℝ)*base91 + (3965629/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (469040582934343701/100000000000000000000000 : ℝ) := by norm_num
    linear_combination (218086961/25000000000000 : ℝ)*(base19) + (36286787/4000000000000 : ℝ)*(base23) + (32339227/50000000000000 : ℝ)*(base32) + (281581/195312500000 : ℝ)*(upper3) + (36451/40000000000 : ℝ)*(upper5) + (419544652050603/50000000000000 : ℝ)*(major0) + (419544652050603/50000000000000 : ℝ)*(major1) + (419544652050603/50000000000000 : ℝ)*(major2) + (265317427/10000000000000 : ℝ)*(sp1) + (2865841257/100000000000000 : ℝ)*(sp2) + (302163786880791/25000000000000 : ℝ)*(sp4) + (24173032440021/2000000000000 : ℝ)*(sp5) + (151081421814029/12500000000000 : ℝ)*(sp6) + (58690404956741/12500000000000 : ℝ)*(sp7) + (234761652166191/50000000000000 : ℝ)*(f.failure) + (302163786880791/25000000000000 : ℝ)*(f.sum) + (196510086761367/100000000000000000000000000000 : ℝ)*base65 + (850114154438633/200000000000000000000000000000 : ℝ)*base68 + (437789582438633/200000000000000000000000000000 : ℝ)*base70 + (1358247724038633/200000000000000000000000000000 : ℝ)*base72 + (194953381761367/100000000000000000000000000000 : ℝ)*base73 + (1291386521238633/200000000000000000000000000000 : ℝ)*base76 + (487191384838633/200000000000000000000000000000 : ℝ)*base78 + (2530785967238633/200000000000000000000000000000 : ℝ)*base80 + (462321577361367/100000000000000000000000000000 : ℝ)*base81 + (2157321/312500000000000000000 : ℝ)*base89 + (2157321/312500000000000000000 : ℝ)*base91 + (2157321/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1646_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11169431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2383/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (11721/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1646_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1646_s1_0 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1607241363/10000000000 : ℝ)*x 0 + (2749653803/5000000000 : ℝ)*x 1 + (5139935697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1607241363/10000000000 : ℝ)^4903 ≤ (1239960886057/12500000000000 : ℝ)^3879 := by
    have hnat : (1607241363 : ℕ)^4903*12500000000000^3879 ≤ 1239960886057^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1607241363 10000000000 1239960886057 12500000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2749653803/5000000000 : ℝ)^4903 ≤ (23481351063589/50000000000000 : ℝ)^3879 := by
    have hnat : (2749653803 : ℕ)^4903*50000000000000^3879 ≤ 23481351063589^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2749653803 5000000000 23481351063589 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5139935697/10000000000 : ℝ)^4903 ≤ (21558805381219/50000000000000 : ℝ)^3879 := by
    have hnat : (5139935697 : ℕ)^4903*50000000000000^3879 ≤ 21558805381219^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5139935697 10000000000 21558805381219 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1607241363/10000000000 : ℝ), (2749653803/5000000000 : ℝ), (5139935697/10000000000 : ℝ)] ![(1239960886057/12500000000000 : ℝ), (23481351063589/50000000000000 : ℝ), (21558805381219/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1607241363/10000000000 : ℝ)|^4903 ≤ (1239960886057/12500000000000 : ℝ)^3879
        have hw : |(-1607241363/10000000000 : ℝ)|=(1607241363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2749653803/5000000000 : ℝ)|^4903 ≤ (23481351063589/50000000000000 : ℝ)^3879
        have hw : |(2749653803/5000000000 : ℝ)|=(2749653803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5139935697/10000000000 : ℝ)|^4903 ≤ (21558805381219/50000000000000 : ℝ)^3879
        have hw : |(5139935697/10000000000 : ℝ)|=(5139935697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s1_1 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2680867223/5000000000 : ℝ)*x 0 + (-28033929/156250000 : ℝ)*x 1 + (642491941/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680867223/5000000000 : ℝ)^4903 ≤ (11370663741741/25000000000000 : ℝ)^3879 := by
    have hnat : (2680867223 : ℕ)^4903*25000000000000^3879 ≤ 11370663741741^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680867223 5000000000 11370663741741 25000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28033929/156250000 : ℝ)^4903 ≤ (11399736050519/100000000000000 : ℝ)^3879 := by
    have hnat : (28033929 : ℕ)^4903*100000000000000^3879 ≤ 11399736050519^3879*156250000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28033929 156250000 11399736050519 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (642491941/1250000000 : ℝ)^4903 ≤ (43117608970489/100000000000000 : ℝ)^3879 := by
    have hnat : (642491941 : ℕ)^4903*100000000000000^3879 ≤ 43117608970489^3879*1250000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642491941 1250000000 43117608970489 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680867223/5000000000 : ℝ), (-28033929/156250000 : ℝ), (642491941/1250000000 : ℝ)] ![(11370663741741/25000000000000 : ℝ), (11399736050519/100000000000000 : ℝ), (43117608970489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680867223/5000000000 : ℝ)|^4903 ≤ (11370663741741/25000000000000 : ℝ)^3879
        have hw : |(2680867223/5000000000 : ℝ)|=(2680867223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-28033929/156250000 : ℝ)|^4903 ≤ (11399736050519/100000000000000 : ℝ)^3879
        have hw : |(-28033929/156250000 : ℝ)|=(28033929/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(642491941/1250000000 : ℝ)|^4903 ≤ (43117608970489/100000000000000 : ℝ)^3879
        have hw : |(642491941/1250000000 : ℝ)|=(642491941/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s1_2 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2680867787/5000000000 : ℝ)*x 0 + (256996713/500000000 : ℝ)*x 1 + (-224271453/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680867787/5000000000 : ℝ)^4903 ≤ (4548266706157/10000000000000 : ℝ)^3879 := by
    have hnat : (2680867787 : ℕ)^4903*10000000000000^3879 ≤ 4548266706157^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680867787 5000000000 4548266706157 10000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256996713/500000000 : ℝ)^4903 ≤ (8623519105113/20000000000000 : ℝ)^3879 := by
    have hnat : (256996713 : ℕ)^4903*20000000000000^3879 ≤ 8623519105113^3879*500000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256996713 500000000 8623519105113 20000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224271453/1250000000 : ℝ)^4903 ≤ (5699868699869/50000000000000 : ℝ)^3879 := by
    have hnat : (224271453 : ℕ)^4903*50000000000000^3879 ≤ 5699868699869^3879*1250000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224271453 1250000000 5699868699869 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680867787/5000000000 : ℝ), (256996713/500000000 : ℝ), (-224271453/1250000000 : ℝ)] ![(4548266706157/10000000000000 : ℝ), (8623519105113/20000000000000 : ℝ), (5699868699869/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680867787/5000000000 : ℝ)|^4903 ≤ (4548266706157/10000000000000 : ℝ)^3879
        have hw : |(2680867787/5000000000 : ℝ)|=(2680867787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(256996713/500000000 : ℝ)|^4903 ≤ (8623519105113/20000000000000 : ℝ)^3879
        have hw : |(256996713/500000000 : ℝ)|=(256996713/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-224271453/1250000000 : ℝ)|^4903 ≤ (5699868699869/50000000000000 : ℝ)^3879
        have hw : |(-224271453/1250000000 : ℝ)|=(224271453/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s1_3 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2088043701/5000000000 : ℝ)*x 0 + (3732179597/10000000000 : ℝ)*x 1 + (4657282971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2088043701/5000000000 : ℝ)^4903 ≤ (16581668468483/50000000000000 : ℝ)^3879 := by
    have hnat : (2088043701 : ℕ)^4903*50000000000000^3879 ≤ 16581668468483^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2088043701 5000000000 16581668468483 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3732179597/10000000000 : ℝ)^4903 ≤ (14385893047991/50000000000000 : ℝ)^3879 := by
    have hnat : (3732179597 : ℕ)^4903*50000000000000^3879 ≤ 14385893047991^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3732179597 10000000000 14385893047991 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4657282971/10000000000 : ℝ)^4903 ≤ (38064876955557/100000000000000 : ℝ)^3879 := by
    have hnat : (4657282971 : ℕ)^4903*100000000000000^3879 ≤ 38064876955557^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4657282971 10000000000 38064876955557 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2088043701/5000000000 : ℝ), (3732179597/10000000000 : ℝ), (4657282971/10000000000 : ℝ)] ![(16581668468483/50000000000000 : ℝ), (14385893047991/50000000000000 : ℝ), (38064876955557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2088043701/5000000000 : ℝ)|^4903 ≤ (16581668468483/50000000000000 : ℝ)^3879
        have hw : |(2088043701/5000000000 : ℝ)|=(2088043701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3732179597/10000000000 : ℝ)|^4903 ≤ (14385893047991/50000000000000 : ℝ)^3879
        have hw : |(3732179597/10000000000 : ℝ)|=(3732179597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4657282971/10000000000 : ℝ)|^4903 ≤ (38064876955557/100000000000000 : ℝ)^3879
        have hw : |(4657282971/10000000000 : ℝ)|=(4657282971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s1_4 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-321480747/2000000000 : ℝ)*x 0 + (1285901241/2500000000 : ℝ)*x 1 + (5495585197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (321480747/2000000000 : ℝ)^4903 ≤ (2480238448679/25000000000000 : ℝ)^3879 := by
    have hnat : (321480747 : ℕ)^4903*25000000000000^3879 ≤ 2480238448679^3879*2000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321480747 2000000000 2480238448679 25000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1285901241/2500000000 : ℝ)^4903 ≤ (21578260296669/50000000000000 : ℝ)^3879 := by
    have hnat : (1285901241 : ℕ)^4903*50000000000000^3879 ≤ 21578260296669^3879*2500000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1285901241 2500000000 21578260296669 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5495585197/10000000000 : ℝ)^4903 ≤ (23461262797049/50000000000000 : ℝ)^3879 := by
    have hnat : (5495585197 : ℕ)^4903*50000000000000^3879 ≤ 23461262797049^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495585197 10000000000 23461262797049 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-321480747/2000000000 : ℝ), (1285901241/2500000000 : ℝ), (5495585197/10000000000 : ℝ)] ![(2480238448679/25000000000000 : ℝ), (21578260296669/50000000000000 : ℝ), (23461262797049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-321480747/2000000000 : ℝ)|^4903 ≤ (2480238448679/25000000000000 : ℝ)^3879
        have hw : |(-321480747/2000000000 : ℝ)|=(321480747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1285901241/2500000000 : ℝ)|^4903 ≤ (21578260296669/50000000000000 : ℝ)^3879
        have hw : |(1285901241/2500000000 : ℝ)|=(1285901241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5495585197/10000000000 : ℝ)|^4903 ≤ (23461262797049/50000000000000 : ℝ)^3879
        have hw : |(5495585197/10000000000 : ℝ)|=(5495585197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s1_5 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2632843759/5000000000 : ℝ)*x 0 + (-179815157/1250000000 : ℝ)*x 1 + (2747792603/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2632843759/5000000000 : ℝ)^4903 ≤ (44455269397677/100000000000000 : ℝ)^3879 := by
    have hnat : (2632843759 : ℕ)^4903*100000000000000^3879 ≤ 44455269397677^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632843759 5000000000 44455269397677 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179815157/1250000000 : ℝ)^4903 ≤ (4311102449929/50000000000000 : ℝ)^3879 := by
    have hnat : (179815157 : ℕ)^4903*50000000000000^3879 ≤ 4311102449929^3879*1250000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179815157 1250000000 4311102449929 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2747792603/5000000000 : ℝ)^4903 ≤ (11730631422807/25000000000000 : ℝ)^3879 := by
    have hnat : (2747792603 : ℕ)^4903*25000000000000^3879 ≤ 11730631422807^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747792603 5000000000 11730631422807 25000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2632843759/5000000000 : ℝ), (-179815157/1250000000 : ℝ), (2747792603/5000000000 : ℝ)] ![(44455269397677/100000000000000 : ℝ), (4311102449929/50000000000000 : ℝ), (11730631422807/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2632843759/5000000000 : ℝ)|^4903 ≤ (44455269397677/100000000000000 : ℝ)^3879
        have hw : |(2632843759/5000000000 : ℝ)|=(2632843759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-179815157/1250000000 : ℝ)|^4903 ≤ (4311102449929/50000000000000 : ℝ)^3879
        have hw : |(-179815157/1250000000 : ℝ)|=(179815157/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2747792603/5000000000 : ℝ)|^4903 ≤ (11730631422807/25000000000000 : ℝ)^3879
        have hw : |(2747792603/5000000000 : ℝ)|=(2747792603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s1_6 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5265687343/10000000000 : ℝ)*x 0 + (274779273/500000000 : ℝ)*x 1 + (-71926057/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5265687343/10000000000 : ℝ)^4903 ≤ (4445526753023/10000000000000 : ℝ)^3879 := by
    have hnat : (5265687343 : ℕ)^4903*10000000000000^3879 ≤ 4445526753023^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265687343 10000000000 4445526753023 10000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274779273/500000000 : ℝ)^4903 ≤ (11730632108111/25000000000000 : ℝ)^3879 := by
    have hnat : (274779273 : ℕ)^4903*25000000000000^3879 ≤ 11730632108111^3879*500000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274779273 500000000 11730632108111 25000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (71926057/500000000 : ℝ)^4903 ≤ (4311102010517/50000000000000 : ℝ)^3879 := by
    have hnat : (71926057 : ℕ)^4903*50000000000000^3879 ≤ 4311102010517^3879*500000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71926057 500000000 4311102010517 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5265687343/10000000000 : ℝ), (274779273/500000000 : ℝ), (-71926057/500000000 : ℝ)] ![(4445526753023/10000000000000 : ℝ), (11730632108111/25000000000000 : ℝ), (4311102010517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5265687343/10000000000 : ℝ)|^4903 ≤ (4445526753023/10000000000000 : ℝ)^3879
        have hw : |(5265687343/10000000000 : ℝ)|=(5265687343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(274779273/500000000 : ℝ)|^4903 ≤ (11730632108111/25000000000000 : ℝ)^3879
        have hw : |(274779273/500000000 : ℝ)|=(274779273/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-71926057/500000000 : ℝ)|^4903 ≤ (4311102010517/50000000000000 : ℝ)^3879
        have hw : |(-71926057/500000000 : ℝ)|=(71926057/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s1_7 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4176501693/10000000000 : ℝ)*x 0 + (2323918093/5000000000 : ℝ)*x 1 + (935440593/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4176501693/10000000000 : ℝ)^4903 ≤ (16583747743557/50000000000000 : ℝ)^3879 := by
    have hnat : (4176501693 : ℕ)^4903*50000000000000^3879 ≤ 16583747743557^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4176501693 10000000000 16583747743557 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2323918093/5000000000 : ℝ)^4903 ≤ (9491827564741/25000000000000 : ℝ)^3879 := by
    have hnat : (2323918093 : ℕ)^4903*25000000000000^3879 ≤ 9491827564741^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2323918093 5000000000 9491827564741 25000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (935440593/2500000000 : ℝ)^4903 ≤ (7216298560959/25000000000000 : ℝ)^3879 := by
    have hnat : (935440593 : ℕ)^4903*25000000000000^3879 ≤ 7216298560959^3879*2500000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935440593 2500000000 7216298560959 25000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4176501693/10000000000 : ℝ), (2323918093/5000000000 : ℝ), (935440593/2500000000 : ℝ)] ![(16583747743557/50000000000000 : ℝ), (9491827564741/25000000000000 : ℝ), (7216298560959/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4176501693/10000000000 : ℝ)|^4903 ≤ (16583747743557/50000000000000 : ℝ)^3879
        have hw : |(4176501693/10000000000 : ℝ)|=(4176501693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2323918093/5000000000 : ℝ)|^4903 ≤ (9491827564741/25000000000000 : ℝ)^3879
        have hw : |(2323918093/5000000000 : ℝ)|=(2323918093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(935440593/2500000000 : ℝ)|^4903 ≤ (7216298560959/25000000000000 : ℝ)^3879
        have hw : |(935440593/2500000000 : ℝ)|=(935440593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1646_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11169431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11721/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2383/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4851/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2167/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (11721/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2383/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (11721/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2383/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (11721/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2383/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (11721/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2383/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (11721/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2383/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (11721/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2383/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2383/50000 : ℝ) ^ (4899/1024 : ℝ) ≤ (23714905750227/50000000000000000000 : ℝ) := by
    have hpowers : (2383/50000 : ℝ)^4899 ≤ (23714905750227/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2383 : ℕ)^4899*50000000000000000000^1024 ≤ 23714905750227^1024*50000^4899 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2383 50000 23714905750227 50000000000000000000 4899 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2383/50000 : ℝ)) (X := (23714905750227/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (11721/50000 : ℝ) ^ (4899/1024 : ℝ) ≤ (96814689523595711/100000000000000000000 : ℝ) := by
    have hpowers : (11721/50000 : ℝ)^4899 ≤ (96814689523595711/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11721 : ℕ)^4899*100000000000000000000^1024 ≤ 96814689523595711^1024*50000^4899 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11721 50000 96814689523595711 100000000000000000000 4899 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11721/50000 : ℝ)) (X := (96814689523595711/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000023714905750227/25000000000000000000 : ℝ) ≤ (2000000396555287/2000000000000000 : ℝ) ^ (4899/1024 : ℝ) := by
    have hpowers : (25000023714905750227/25000000000000000000 : ℝ)^1024 ≤ (2000000396555287/2000000000000000 : ℝ)^4899 := by
      have hnat : (25000023714905750227 : ℕ)^1024*2000000000000000^4899 ≤ 2000000396555287^4899*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000023714905750227 25000000000000000000 2000000396555287 2000000000000000 1024 4899 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000396555287/2000000000000000 : ℝ)) (X := (25000023714905750227/25000000000000000000 : ℝ)) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20019372423867019233/20000000000000000000 : ℝ) ≤ (1000202385866057/1000000000000000 : ℝ) ^ (4899/1024 : ℝ) := by
    have hpowers : (20019372423867019233/20000000000000000000 : ℝ)^1024 ≤ (1000202385866057/1000000000000000 : ℝ)^4899 := by
      have hnat : (20019372423867019233 : ℕ)^1024*1000000000000000^4899 ≤ 1000202385866057^4899*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20019372423867019233 20000000000000000000 1000202385866057 1000000000000000 1024 4899 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000202385866057/1000000000000000 : ℝ)) (X := (20019372423867019233/20000000000000000000 : ℝ)) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50096814689523595711/50000000000000000000 : ℝ) ≤ (2000809146908941/2000000000000000 : ℝ) ^ (4899/1024 : ℝ) := by
    have hpowers : (50096814689523595711/50000000000000000000 : ℝ)^1024 ≤ (2000809146908941/2000000000000000 : ℝ)^4899 := by
      have hnat : (50096814689523595711 : ℕ)^1024*2000000000000000^4899 ≤ 2000809146908941^4899*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50096814689523595711 50000000000000000000 2000809146908941 2000000000000000 1024 4899 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000809146908941/2000000000000000 : ℝ)) (X := (50096814689523595711/50000000000000000000 : ℝ)) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(23714905750227/50000000000000000000 : ℝ) ≤ ((4668519112735128131/4669000000000000000 : ℝ)+2*(404375176827/373520000000000 : ℝ)*(2383/50000 : ℝ))^(4899/1024 : ℝ) := by
    rw [show (4668519112735128131/4669000000000000000 : ℝ)+2*(404375176827/373520000000000 : ℝ)*(2383/50000 : ℝ)=(2000000396555287/2000000000000000 : ℝ) by norm_num, show 1+2*(23714905750227/50000000000000000000 : ℝ)=(25000023714905750227/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(96814689523595711/100000000000000000000 : ℝ)+(23714905750227/50000000000000000000 : ℝ) ≤ ((4668519112735128131/4669000000000000000 : ℝ)+(404375176827/373520000000000 : ℝ)*((11721/50000 : ℝ)+(2383/50000 : ℝ)))^(4899/1024 : ℝ) := by
    rw [show (4668519112735128131/4669000000000000000 : ℝ)+(404375176827/373520000000000 : ℝ)*((11721/50000 : ℝ)+(2383/50000 : ℝ))=(1000202385866057/1000000000000000 : ℝ) by norm_num, show 1+(96814689523595711/100000000000000000000 : ℝ)+(23714905750227/50000000000000000000 : ℝ)=(20019372423867019233/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(96814689523595711/100000000000000000000 : ℝ) ≤ ((4668519112735128131/4669000000000000000 : ℝ)+2*(404375176827/373520000000000 : ℝ)*(11721/50000 : ℝ))^(4899/1024 : ℝ) := by
    rw [show (4668519112735128131/4669000000000000000 : ℝ)+2*(404375176827/373520000000000 : ℝ)*(11721/50000 : ℝ)=(2000809146908941/2000000000000000 : ℝ) by norm_num, show 1+2*(96814689523595711/100000000000000000000 : ℝ)=(50096814689523595711/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4668519112735128131/4669000000000000000 : ℝ)*(X 1 0+X 2 0)+(404375176827/373520000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4899/1024 : ℝ)) (lo := (2383/50000 : ℝ)) (hi := (11721/50000 : ℝ)) (c := (4668519112735128131/4669000000000000000 : ℝ)) (alpha := (404375176827/373520000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4668519112735128131/4669000000000000000 : ℝ)*(X 0 1+X 2 1)+(404375176827/373520000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4899/1024 : ℝ)) (lo := (2383/50000 : ℝ)) (hi := (11721/50000 : ℝ)) (c := (4668519112735128131/4669000000000000000 : ℝ)) (alpha := (404375176827/373520000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4668519112735128131/4669000000000000000 : ℝ)*(X 0 2+X 1 2)+(404375176827/373520000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4899/1024 : ℝ)) (lo := (2383/50000 : ℝ)) (hi := (11721/50000 : ℝ)) (c := (4668519112735128131/4669000000000000000 : ℝ)) (alpha := (404375176827/373520000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1607241363/10000000000 : ℝ)*X 0 0+(2749653803/5000000000 : ℝ)*X 0 1+(5139935697/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2680867223/5000000000 : ℝ)*X 1 0+(-28033929/156250000 : ℝ)*X 1 1+(642491941/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2680867787/5000000000 : ℝ)*X 2 0+(256996713/500000000 : ℝ)*X 2 1+(-224271453/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2088043701/5000000000 : ℝ)*X 0 0+(3732179597/10000000000 : ℝ)*X 0 1+(4657282971/10000000000 : ℝ)*X 0 2+(2088043701/5000000000 : ℝ)*X 1 0+(3732179597/10000000000 : ℝ)*X 1 1+(4657282971/10000000000 : ℝ)*X 1 2+(2088043701/5000000000 : ℝ)*X 2 0+(3732179597/10000000000 : ℝ)*X 2 1+(4657282971/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-321480747/2000000000 : ℝ)*X 0 0+(1285901241/2500000000 : ℝ)*X 0 1+(5495585197/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2632843759/5000000000 : ℝ)*X 1 0+(-179815157/1250000000 : ℝ)*X 1 1+(2747792603/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5265687343/10000000000 : ℝ)*X 2 0+(274779273/500000000 : ℝ)*X 2 1+(-71926057/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4176501693/10000000000 : ℝ)*X 0 0+(2323918093/5000000000 : ℝ)*X 0 1+(935440593/2500000000 : ℝ)*X 0 2+(4176501693/10000000000 : ℝ)*X 1 0+(2323918093/5000000000 : ℝ)*X 1 1+(935440593/2500000000 : ℝ)*X 1 2+(4176501693/10000000000 : ℝ)*X 2 0+(2323918093/5000000000 : ℝ)*X 2 1+(935440593/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46326496412067853866723987/4025000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (698872453/100000000000000 : ℝ)*(base1) + (76741417/6250000000000 : ℝ)*(base19) + (1813272019/100000000000000 : ℝ)*(base23) + (120183491/100000000000000 : ℝ)*(upper3) + (107068159/100000000000000 : ℝ)*(upper5) + (1931798916960139/100000000000000 : ℝ)*(major0) + (1931798916960139/100000000000000 : ℝ)*(major1) + (1931798916960139/100000000000000 : ℝ)*(major2) + (1391316514779887/50000000000000 : ℝ)*(sp0) + (556526616028537/20000000000000 : ℝ)*(sp1) + (1391316247366669/50000000000000 : ℝ)*(sp2) + (1080960959346477/100000000000000 : ℝ)*(sp3) + (494329509/25000000000000 : ℝ)*(sp4) + (742019847/50000000000000 : ℝ)*(sp7) + (540481571129311/50000000000000 : ℝ)*(f.failure) + (1391317154002679/50000000000000 : ℝ)*(f.sum) + (18669734493729/18676000000000000000000000000 : ℝ)*base65 + (37021340444940387/66700000000000000000000000000000 : ℝ)*base67 + (575521502368140387/66700000000000000000000000000000 : ℝ)*base69 + (34457288008559613/66700000000000000000000000000000 : ℝ)*base72 + (7870272943937/3735200000000000000000000000 : ℝ)*base73 + (511473020131140387/66700000000000000000000000000000 : ℝ)*base75 + (416505513908040387/66700000000000000000000000000000 : ℝ)*base77 + (24735992040540387/66700000000000000000000000000000 : ℝ)*base79 + (13900607932601/3735200000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3082959/312500000000000000000 : ℝ)*base90 + (3082959/312500000000000000000 : ℝ)*base92 + (3082959/312500000000000000000 : ℝ)*base94 + (1/50000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (107555773438543094052080883/10150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1963506183/100000000000000 : ℝ)*(base19) + (235965571/12500000000000 : ℝ)*(base23) + (392107/50000000000000 : ℝ)*(upper2) + (25710103/10000000000000 : ℝ)*(upper3) + (62001869/25000000000000 : ℝ)*(upper5) + (1972365707547471/100000000000000 : ℝ)*(major0) + (1972365707547471/100000000000000 : ℝ)*(major1) + (1972365707547471/100000000000000 : ℝ)*(major2) + (17711264771/100000000000000 : ℝ)*(sp1) + (18651199781/100000000000000 : ℝ)*(sp2) + (2841068245731297/100000000000000 : ℝ)*(sp4) + (2841048570960343/100000000000000 : ℝ)*(sp5) + (710261926701737/25000000000000 : ℝ)*(sp6) + (1103662816142711/100000000000000 : ℝ)*(sp7) + (1103662816142711/100000000000000 : ℝ)*(f.failure) + (2841068245731297/100000000000000 : ℝ)*(f.sum) + (38027390878811/18676000000000000000000000000 : ℝ)*base66 + (147897519604447257/66700000000000000000000000000000 : ℝ)*base68 + (147562848819347257/66700000000000000000000000000000 : ℝ)*base70 + (236322490594747257/66700000000000000000000000000000 : ℝ)*base72 + (15015731871239/3735200000000000000000000000 : ℝ)*base74 + (164128409927247257/66700000000000000000000000000000 : ℝ)*base76 + (522576740725347257/66700000000000000000000000000000 : ℝ)*base78 + (138747268898847257/66700000000000000000000000000000 : ℝ)*base80 + (11223835761189/18676000000000000000000000000 : ℝ)*base81 + (2917441/625000000000000000000 : ℝ)*base89 + (2917441/625000000000000000000 : ℝ)*base91 + (2917441/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1646_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11169431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (11721/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2383/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4851/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2167/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1646_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1646_s2_0 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-161692983/1000000000 : ℝ)*x 0 + (1090505797/2000000000 : ℝ)*x 1 + (1295081797/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (161692983/1000000000 : ℝ)^4903 ≤ (2498832095691/25000000000000 : ℝ)^3879 := by
    have hnat : (161692983 : ℕ)^4903*25000000000000^3879 ≤ 2498832095691^3879*1000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161692983 1000000000 2498832095691 25000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090505797/2000000000 : ℝ)^4903 ≤ (23229168131717/50000000000000 : ℝ)^3879 := by
    have hnat : (1090505797 : ℕ)^4903*50000000000000^3879 ≤ 23229168131717^3879*2000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090505797 2000000000 23229168131717 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295081797/2500000000 : ℝ)^4903 ≤ (21773167666079/50000000000000 : ℝ)^3879 := by
    have hnat : (1295081797 : ℕ)^4903*50000000000000^3879 ≤ 21773167666079^3879*2500000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295081797 2500000000 21773167666079 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-161692983/1000000000 : ℝ), (1090505797/2000000000 : ℝ), (1295081797/2500000000 : ℝ)] ![(2498832095691/25000000000000 : ℝ), (23229168131717/50000000000000 : ℝ), (21773167666079/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-161692983/1000000000 : ℝ)|^4903 ≤ (2498832095691/25000000000000 : ℝ)^3879
        have hw : |(-161692983/1000000000 : ℝ)|=(161692983/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090505797/2000000000 : ℝ)|^4903 ≤ (23229168131717/50000000000000 : ℝ)^3879
        have hw : |(1090505797/2000000000 : ℝ)|=(1090505797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295081797/2500000000 : ℝ)|^4903 ≤ (21773167666079/50000000000000 : ℝ)^3879
        have hw : |(1295081797/2500000000 : ℝ)|=(1295081797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s2_1 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349370389/10000000000 : ℝ)*x 0 + (-878593961/5000000000 : ℝ)*x 1 + (51803279/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349370389/10000000000 : ℝ)^4903 ≤ (22675062920001/50000000000000 : ℝ)^3879 := by
    have hnat : (5349370389 : ℕ)^4903*50000000000000^3879 ≤ 22675062920001^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349370389 10000000000 22675062920001 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (878593961/5000000000 : ℝ)^4903 ≤ (11103531248517/100000000000000 : ℝ)^3879 := by
    have hnat : (878593961 : ℕ)^4903*100000000000000^3879 ≤ 11103531248517^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      878593961 5000000000 11103531248517 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51803279/100000000 : ℝ)^4903 ≤ (43546342897291/100000000000000 : ℝ)^3879 := by
    have hnat : (51803279 : ℕ)^4903*100000000000000^3879 ≤ 43546342897291^3879*100000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51803279 100000000 43546342897291 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349370389/10000000000 : ℝ), (-878593961/5000000000 : ℝ), (51803279/100000000 : ℝ)] ![(22675062920001/50000000000000 : ℝ), (11103531248517/100000000000000 : ℝ), (43546342897291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349370389/10000000000 : ℝ)|^4903 ≤ (22675062920001/50000000000000 : ℝ)^3879
        have hw : |(5349370389/10000000000 : ℝ)|=(5349370389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-878593961/5000000000 : ℝ)|^4903 ≤ (11103531248517/100000000000000 : ℝ)^3879
        have hw : |(-878593961/5000000000 : ℝ)|=(878593961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(51803279/100000000 : ℝ)|^4903 ≤ (43546342897291/100000000000000 : ℝ)^3879
        have hw : |(51803279/100000000 : ℝ)|=(51803279/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s2_2 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674686103/5000000000 : ℝ)*x 0 + (1036065323/2000000000 : ℝ)*x 1 + (-878593597/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674686103/5000000000 : ℝ)^4903 ≤ (5668768163789/12500000000000 : ℝ)^3879 := by
    have hnat : (2674686103 : ℕ)^4903*12500000000000^3879 ≤ 5668768163789^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674686103 5000000000 5668768163789 12500000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036065323/2000000000 : ℝ)^4903 ≤ (43546329243927/100000000000000 : ℝ)^3879 := by
    have hnat : (1036065323 : ℕ)^4903*100000000000000^3879 ≤ 43546329243927^3879*2000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036065323 2000000000 43546329243927 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (878593597/5000000000 : ℝ)^4903 ≤ (2775881358491/25000000000000 : ℝ)^3879 := by
    have hnat : (878593597 : ℕ)^4903*25000000000000^3879 ≤ 2775881358491^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      878593597 5000000000 2775881358491 25000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674686103/5000000000 : ℝ), (1036065323/2000000000 : ℝ), (-878593597/5000000000 : ℝ)] ![(5668768163789/12500000000000 : ℝ), (43546329243927/100000000000000 : ℝ), (2775881358491/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674686103/5000000000 : ℝ)|^4903 ≤ (5668768163789/12500000000000 : ℝ)^3879
        have hw : |(2674686103/5000000000 : ℝ)|=(2674686103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036065323/2000000000 : ℝ)|^4903 ≤ (43546329243927/100000000000000 : ℝ)^3879
        have hw : |(1036065323/2000000000 : ℝ)|=(1036065323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-878593597/5000000000 : ℝ)|^4903 ≤ (2775881358491/25000000000000 : ℝ)^3879
        have hw : |(-878593597/5000000000 : ℝ)|=(878593597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s2_3 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (83666033/200000000 : ℝ)*x 0 + (3843649587/10000000000 : ℝ)*x 1 + (2272178087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83666033/200000000 : ℝ)^4903 ≤ (33235767322941/100000000000000 : ℝ)^3879 := by
    have hnat : (83666033 : ℕ)^4903*100000000000000^3879 ≤ 33235767322941^3879*200000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83666033 200000000 33235767322941 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3843649587/10000000000 : ℝ)^4903 ≤ (29862223560869/100000000000000 : ℝ)^3879 := by
    have hnat : (3843649587 : ℕ)^4903*100000000000000^3879 ≤ 29862223560869^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3843649587 10000000000 29862223560869 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2272178087/5000000000 : ℝ)^4903 ≤ (3690200909799/10000000000000 : ℝ)^3879 := by
    have hnat : (2272178087 : ℕ)^4903*10000000000000^3879 ≤ 3690200909799^3879*5000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2272178087 5000000000 3690200909799 10000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83666033/200000000 : ℝ), (3843649587/10000000000 : ℝ), (2272178087/5000000000 : ℝ)] ![(33235767322941/100000000000000 : ℝ), (29862223560869/100000000000000 : ℝ), (3690200909799/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83666033/200000000 : ℝ)|^4903 ≤ (33235767322941/100000000000000 : ℝ)^3879
        have hw : |(83666033/200000000 : ℝ)|=(83666033/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3843649587/10000000000 : ℝ)|^4903 ≤ (29862223560869/100000000000000 : ℝ)^3879
        have hw : |(3843649587/10000000000 : ℝ)|=(3843649587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2272178087/5000000000 : ℝ)|^4903 ≤ (3690200909799/10000000000000 : ℝ)^3879
        have hw : |(2272178087/5000000000 : ℝ)|=(2272178087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s2_4 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1616998863/10000000000 : ℝ)*x 0 + (1295609633/2500000000 : ℝ)*x 1 + (5450395687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1616998863/10000000000 : ℝ)^4903 ≤ (4997933889059/50000000000000 : ℝ)^3879 := by
    have hnat : (1616998863 : ℕ)^4903*50000000000000^3879 ≤ 4997933889059^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1616998863 10000000000 4997933889059 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295609633/2500000000 : ℝ)^4903 ≤ (43568769961289/100000000000000 : ℝ)^3879 := by
    have hnat : (1295609633 : ℕ)^4903*100000000000000^3879 ≤ 43568769961289^3879*2500000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295609633 2500000000 43568769961289 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5450395687/10000000000 : ℝ)^4903 ≤ (46435362249539/100000000000000 : ℝ)^3879 := by
    have hnat : (5450395687 : ℕ)^4903*100000000000000^3879 ≤ 46435362249539^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450395687 10000000000 46435362249539 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1616998863/10000000000 : ℝ), (1295609633/2500000000 : ℝ), (5450395687/10000000000 : ℝ)] ![(4997933889059/50000000000000 : ℝ), (43568769961289/100000000000000 : ℝ), (46435362249539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1616998863/10000000000 : ℝ)|^4903 ≤ (4997933889059/50000000000000 : ℝ)^3879
        have hw : |(-1616998863/10000000000 : ℝ)|=(1616998863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295609633/2500000000 : ℝ)|^4903 ≤ (43568769961289/100000000000000 : ℝ)^3879
        have hw : |(1295609633/2500000000 : ℝ)|=(1295609633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5450395687/10000000000 : ℝ)|^4903 ≤ (46435362249539/100000000000000 : ℝ)^3879
        have hw : |(5450395687/10000000000 : ℝ)|=(5450395687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s2_5 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276682133/10000000000 : ℝ)*x 0 + (-1487119733/10000000000 : ℝ)*x 1 + (5450394959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276682133/10000000000 : ℝ)^4903 ≤ (4457262664539/10000000000000 : ℝ)^3879 := by
    have hnat : (5276682133 : ℕ)^4903*10000000000000^3879 ≤ 4457262664539^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276682133 10000000000 4457262664539 10000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1487119733/10000000000 : ℝ)^4903 ≤ (899201892491/10000000000000 : ℝ)^3879 := by
    have hnat : (1487119733 : ℕ)^4903*10000000000000^3879 ≤ 899201892491^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1487119733 10000000000 899201892491 10000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5450394959/10000000000 : ℝ)^4903 ≤ (11608838602483/25000000000000 : ℝ)^3879 := by
    have hnat : (5450394959 : ℕ)^4903*25000000000000^3879 ≤ 11608838602483^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450394959 10000000000 11608838602483 25000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276682133/10000000000 : ℝ), (-1487119733/10000000000 : ℝ), (5450394959/10000000000 : ℝ)] ![(4457262664539/10000000000000 : ℝ), (899201892491/10000000000000 : ℝ), (11608838602483/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276682133/10000000000 : ℝ)|^4903 ≤ (4457262664539/10000000000000 : ℝ)^3879
        have hw : |(5276682133/10000000000 : ℝ)|=(5276682133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1487119733/10000000000 : ℝ)|^4903 ≤ (899201892491/10000000000000 : ℝ)^3879
        have hw : |(-1487119733/10000000000 : ℝ)|=(1487119733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5450394959/10000000000 : ℝ)|^4903 ≤ (11608838602483/25000000000000 : ℝ)^3879
        have hw : |(5450394959/10000000000 : ℝ)|=(5450394959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s2_6 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276682983/10000000000 : ℝ)*x 0 + (1090078909/2000000000 : ℝ)*x 1 + (-1487119129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276682983/10000000000 : ℝ)^4903 ≤ (11143158930211/25000000000000 : ℝ)^3879 := by
    have hnat : (5276682983 : ℕ)^4903*25000000000000^3879 ≤ 11143158930211^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276682983 10000000000 11143158930211 25000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090078909/2000000000 : ℝ)^4903 ≤ (23217674975847/50000000000000 : ℝ)^3879 := by
    have hnat : (1090078909 : ℕ)^4903*50000000000000^3879 ≤ 23217674975847^3879*2000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090078909 2000000000 23217674975847 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1487119129/10000000000 : ℝ)^4903 ≤ (8992014308649/100000000000000 : ℝ)^3879 := by
    have hnat : (1487119129 : ℕ)^4903*100000000000000^3879 ≤ 8992014308649^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1487119129 10000000000 8992014308649 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276682983/10000000000 : ℝ), (1090078909/2000000000 : ℝ), (-1487119129/10000000000 : ℝ)] ![(11143158930211/25000000000000 : ℝ), (23217674975847/50000000000000 : ℝ), (8992014308649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276682983/10000000000 : ℝ)|^4903 ≤ (11143158930211/25000000000000 : ℝ)^3879
        have hw : |(5276682983/10000000000 : ℝ)|=(5276682983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090078909/2000000000 : ℝ)|^4903 ≤ (23217674975847/50000000000000 : ℝ)^3879
        have hw : |(1090078909/2000000000 : ℝ)|=(1090078909/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1487119129/10000000000 : ℝ)|^4903 ≤ (8992014308649/100000000000000 : ℝ)^3879
        have hw : |(-1487119129/10000000000 : ℝ)|=(1487119129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1646_s2_7 (p : ℝ) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4183483123/10000000000 : ℝ)*x 0 + (907784219/2000000000 : ℝ)*x 1 + (3849142821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4183483123/10000000000 : ℝ)^4903 ≤ (33237589720593/100000000000000 : ℝ)^3879 := by
    have hnat : (4183483123 : ℕ)^4903*100000000000000^3879 ≤ 33237589720593^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4183483123 10000000000 33237589720593 100000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (907784219/2000000000 : ℝ)^4903 ≤ (18423115927847/50000000000000 : ℝ)^3879 := by
    have hnat : (907784219 : ℕ)^4903*50000000000000^3879 ≤ 18423115927847^3879*2000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907784219 2000000000 18423115927847 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3849142821/10000000000 : ℝ)^4903 ≤ (14958089203413/50000000000000 : ℝ)^3879 := by
    have hnat : (3849142821 : ℕ)^4903*50000000000000^3879 ≤ 14958089203413^3879*10000000000^4903 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3849142821 10000000000 14958089203413 50000000000000 4903 3879 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4903/1024 : ℝ)) 4903 3879 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4183483123/10000000000 : ℝ), (907784219/2000000000 : ℝ), (3849142821/10000000000 : ℝ)] ![(33237589720593/100000000000000 : ℝ), (18423115927847/50000000000000 : ℝ), (14958089203413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4183483123/10000000000 : ℝ)|^4903 ≤ (33237589720593/100000000000000 : ℝ)^3879
        have hw : |(4183483123/10000000000 : ℝ)|=(4183483123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(907784219/2000000000 : ℝ)|^4903 ≤ (18423115927847/50000000000000 : ℝ)^3879
        have hw : |(907784219/2000000000 : ℝ)|=(907784219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3849142821/10000000000 : ℝ)|^4903 ≤ (14958089203413/50000000000000 : ℝ)^3879
        have hw : |(3849142821/10000000000 : ℝ)|=(3849142821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1646_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11169431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2167/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4851/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (423/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16359/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2167/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4851/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2167/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4851/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2167/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4851/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2167/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4851/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2167/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4851/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2167/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4851/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4851/50000 : ℝ) ^ (4899/1024 : ℝ) ≤ (1422205221242387/100000000000000000000 : ℝ) := by
    have hpowers : (4851/50000 : ℝ)^4899 ≤ (1422205221242387/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4851 : ℕ)^4899*100000000000000000000^1024 ≤ 1422205221242387^1024*50000^4899 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4851 50000 1422205221242387 100000000000000000000 4899 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4851/50000 : ℝ)) (X := (1422205221242387/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2167/12500 : ℝ) ^ (4899/1024 : ℝ) ≤ (4571142644164163/20000000000000000000 : ℝ) := by
    have hpowers : (2167/12500 : ℝ)^4899 ≤ (4571142644164163/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2167 : ℕ)^4899*20000000000000000000^1024 ≤ 4571142644164163^1024*12500^4899 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2167 12500 4571142644164163 20000000000000000000 4899 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2167/12500 : ℝ)) (X := (4571142644164163/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001422205221242387/50000000000000000000 : ℝ) ≤ (1000005945383809/1000000000000000 : ℝ) ^ (4899/1024 : ℝ) := by
    have hpowers : (50001422205221242387/50000000000000000000 : ℝ)^1024 ≤ (1000005945383809/1000000000000000 : ℝ)^4899 := by
      have hnat : (50001422205221242387 : ℕ)^1024*1000000000000000^4899 ≤ 1000005945383809^4899*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001422205221242387 50000000000000000000 1000005945383809 1000000000000000 1024 4899 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000005945383809/1000000000000000 : ℝ)) (X := (50001422205221242387/50000000000000000000 : ℝ)) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50012138959221031601/50000000000000000000 : ℝ) ≤ (10000507413794749/10000000000000000 : ℝ) ^ (4899/1024 : ℝ) := by
    have hpowers : (50012138959221031601/50000000000000000000 : ℝ)^1024 ≤ (10000507413794749/10000000000000000 : ℝ)^4899 := by
      have hnat : (50012138959221031601 : ℕ)^1024*10000000000000000^4899 ≤ 10000507413794749^4899*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012138959221031601 50000000000000000000 10000507413794749 10000000000000000 1024 4899 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000507413794749/10000000000000000 : ℝ)) (X := (50012138959221031601/50000000000000000000 : ℝ)) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10004571142644164163/10000000000000000000 : ℝ) ≤ (625059710859463/625000000000000 : ℝ) ^ (4899/1024 : ℝ) := by
    have hpowers : (10004571142644164163/10000000000000000000 : ℝ)^1024 ≤ (625059710859463/625000000000000 : ℝ)^4899 := by
      have hnat : (10004571142644164163 : ℕ)^1024*625000000000000^4899 ≤ 625059710859463^4899*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004571142644164163 10000000000000000000 625059710859463 625000000000000 1024 4899 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625059710859463/625000000000000 : ℝ)) (X := (10004571142644164163/10000000000000000000 : ℝ)) (by norm_num) 4899 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1422205221242387/100000000000000000000 : ℝ) ≤ ((433703191225005499/433750000000000000 : ℝ)+2*(447959956659/763400000000000 : ℝ)*(4851/50000 : ℝ))^(4899/1024 : ℝ) := by
    rw [show (433703191225005499/433750000000000000 : ℝ)+2*(447959956659/763400000000000 : ℝ)*(4851/50000 : ℝ)=(1000005945383809/1000000000000000 : ℝ) by norm_num, show 1+2*(1422205221242387/100000000000000000000 : ℝ)=(50001422205221242387/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4571142644164163/20000000000000000000 : ℝ)+(1422205221242387/100000000000000000000 : ℝ) ≤ ((433703191225005499/433750000000000000 : ℝ)+(447959956659/763400000000000 : ℝ)*((2167/12500 : ℝ)+(4851/50000 : ℝ)))^(4899/1024 : ℝ) := by
    rw [show (433703191225005499/433750000000000000 : ℝ)+(447959956659/763400000000000 : ℝ)*((2167/12500 : ℝ)+(4851/50000 : ℝ))=(10000507413794749/10000000000000000 : ℝ) by norm_num, show 1+(4571142644164163/20000000000000000000 : ℝ)+(1422205221242387/100000000000000000000 : ℝ)=(50012138959221031601/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4571142644164163/20000000000000000000 : ℝ) ≤ ((433703191225005499/433750000000000000 : ℝ)+2*(447959956659/763400000000000 : ℝ)*(2167/12500 : ℝ))^(4899/1024 : ℝ) := by
    rw [show (433703191225005499/433750000000000000 : ℝ)+2*(447959956659/763400000000000 : ℝ)*(2167/12500 : ℝ)=(625059710859463/625000000000000 : ℝ) by norm_num, show 1+2*(4571142644164163/20000000000000000000 : ℝ)=(10004571142644164163/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (433703191225005499/433750000000000000 : ℝ)*(X 1 0+X 2 0)+(447959956659/763400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4899/1024 : ℝ)) (lo := (4851/50000 : ℝ)) (hi := (2167/12500 : ℝ)) (c := (433703191225005499/433750000000000000 : ℝ)) (alpha := (447959956659/763400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (433703191225005499/433750000000000000 : ℝ)*(X 0 1+X 2 1)+(447959956659/763400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4899/1024 : ℝ)) (lo := (4851/50000 : ℝ)) (hi := (2167/12500 : ℝ)) (c := (433703191225005499/433750000000000000 : ℝ)) (alpha := (447959956659/763400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (433703191225005499/433750000000000000 : ℝ)*(X 0 2+X 1 2)+(447959956659/763400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4899/1024 : ℝ)) (lo := (4851/50000 : ℝ)) (hi := (2167/12500 : ℝ)) (c := (433703191225005499/433750000000000000 : ℝ)) (alpha := (447959956659/763400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-161692983/1000000000 : ℝ)*X 0 0+(1090505797/2000000000 : ℝ)*X 0 1+(1295081797/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349370389/10000000000 : ℝ)*X 1 0+(-878593961/5000000000 : ℝ)*X 1 1+(51803279/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674686103/5000000000 : ℝ)*X 2 0+(1036065323/2000000000 : ℝ)*X 2 1+(-878593597/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((83666033/200000000 : ℝ)*X 0 0+(3843649587/10000000000 : ℝ)*X 0 1+(2272178087/5000000000 : ℝ)*X 0 2+(83666033/200000000 : ℝ)*X 1 0+(3843649587/10000000000 : ℝ)*X 1 1+(2272178087/5000000000 : ℝ)*X 1 2+(83666033/200000000 : ℝ)*X 2 0+(3843649587/10000000000 : ℝ)*X 2 1+(2272178087/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1616998863/10000000000 : ℝ)*X 0 0+(1295609633/2500000000 : ℝ)*X 0 1+(5450395687/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5276682133/10000000000 : ℝ)*X 1 0+(-1487119733/10000000000 : ℝ)*X 1 1+(5450394959/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5276682983/10000000000 : ℝ)*X 2 0+(1090078909/2000000000 : ℝ)*X 2 1+(-1487119129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4183483123/10000000000 : ℝ)*X 0 0+(907784219/2000000000 : ℝ)*X 0 1+(3849142821/10000000000 : ℝ)*X 0 2+(4183483123/10000000000 : ℝ)*X 1 0+(907784219/2000000000 : ℝ)*X 1 1+(3849142821/10000000000 : ℝ)*X 1 2+(4183483123/10000000000 : ℝ)*X 2 0+(907784219/2000000000 : ℝ)*X 2 1+(3849142821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1646_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (93482845823240508052908459/29820312500000000000000000000000 : ℝ) := by norm_num
    linear_combination (104913177/100000000000000 : ℝ)*(base19) + (522860689/50000000000000 : ℝ)*(base23) + (47751227/25000000000000 : ℝ)*(upper4) + (150259077/50000000000000 : ℝ)*(upper5) + (1275224091121221/50000000000000 : ℝ)*(major0) + (1275224091121221/50000000000000 : ℝ)*(major1) + (1275224091121221/50000000000000 : ℝ)*(major2) + (3673744657959139/100000000000000 : ℝ)*(sp0) + (918439027675541/25000000000000 : ℝ)*(sp1) + (183687942541473/5000000000000 : ℝ)*(sp2) + (713566679079073/50000000000000 : ℝ)*(sp3) + (152385917/1000000000000 : ℝ)*(sp4) + (3680935499/100000000000000 : ℝ)*(sp5) + (187830011/6250000000000 : ℝ)*(sp7) + (713568181719161/50000000000000 : ℝ)*(f.failure) + (3673759896550839/100000000000000 : ℝ)*(f.sum) + (77458178672991/19085000000000000000000000000 : ℝ)*base66 + (1500960944614968319/238562500000000000000000000000000 : ℝ)*base67 + (1436727467845280819/238562500000000000000000000000000 : ℝ)*base69 + (331185928244906681/238562500000000000000000000000000 : ℝ)*base72 + (1655460418839/4771250000000000000000000000 : ℝ)*base74 + (1216163051091968319/238562500000000000000000000000000 : ℝ)*base75 + (1822692875645780819/238562500000000000000000000000000 : ℝ)*base77 + (3737353271743405819/238562500000000000000000000000000 : ℝ)*base79 + (25619837225461/19085000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (1082609/312500000000000000000 : ℝ)*base90 + (1082609/312500000000000000000 : ℝ)*base92 + (1082609/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1085623912234011606528651837/119281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27572033/4000000000000 : ℝ)*(base19) + (2224049581/100000000000000 : ℝ)*(base23) + (384042797/100000000000000 : ℝ)*(lower4) + (185450867/100000000000000 : ℝ)*(upper5) + (1295421014840287/50000000000000 : ℝ)*(major0) + (1295421014840287/50000000000000 : ℝ)*(major1) + (1295421014840287/50000000000000 : ℝ)*(major2) + (1439022299/100000000000000 : ℝ)*(sp0) + (2991203399/100000000000000 : ℝ)*(sp1) + (3585752469/20000000000000 : ℝ)*(sp2) + (1865971526109789/50000000000000 : ℝ)*(sp4) + (3731940810737653/100000000000000 : ℝ)*(sp5) + (911114340437/24414062500 : ℝ)*(sp6) + (1449739264739949/100000000000000 : ℝ)*(sp7) + (1449739264739949/100000000000000 : ℝ)*(f.failure) + (1865972245620939/50000000000000 : ℝ)*(f.sum) + (17176175372011/9542500000000000000000000000 : ℝ)*base66 + (1348701679845173407/238562500000000000000000000000000 : ℝ)*base68 + (485926385672485907/238562500000000000000000000000000 : ℝ)*base70 + (187247414367485907/238562500000000000000000000000000 : ℝ)*base72 + (36070170314247/19085000000000000000000000000 : ℝ)*base74 + (1927105834215798407/238562500000000000000000000000000 : ℝ)*base76 + (2276120662107610907/238562500000000000000000000000000 : ℝ)*base78 + (3626474483049423407/238562500000000000000000000000000 : ℝ)*base80 + (4854282834449/9542500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (5799019/625000000000000000000 : ℝ)*base89 + (5799019/625000000000000000000 : ℝ)*base91 + (5799019/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1646_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11169431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2167/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4851/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (423/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16359/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1646_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1646_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11169431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (423/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16359/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1646_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1646_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1646_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4899/1024 : ℝ) ≤ p) (hpb : p ≤ (4903/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (11169431/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (423/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16359/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1646_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
