-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1474_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:11:40.838862+00:00
-- url     : https://prove2.me/submissions/536bb3e6-60be-4b9b-836e-d0b6c1476d24

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
theorem support_rectangle_w1474_s6_0 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-3008827/15625000 : ℝ)*x 0 + (543822329/1000000000 : ℝ)*x 1 + (325967149/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3008827/15625000 : ℝ)^4445 ≤ (11760650413987/100000000000000 : ℝ)^3421 := by
    have hnat : (3008827 : ℕ)^4445*100000000000000^3421 ≤ 11760650413987^3421*15625000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3008827 15625000 11760650413987 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (543822329/1000000000 : ℝ)^4445 ≤ (45318132318451/100000000000000 : ℝ)^3421 := by
    have hnat : (543822329 : ℕ)^4445*100000000000000^3421 ≤ 45318132318451^3421*1000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543822329 1000000000 45318132318451 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (325967149/625000000 : ℝ)^4445 ≤ (21460608627963/50000000000000 : ℝ)^3421 := by
    have hnat : (325967149 : ℕ)^4445*50000000000000^3421 ≤ 21460608627963^3421*625000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325967149 625000000 21460608627963 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3008827/15625000 : ℝ), (543822329/1000000000 : ℝ), (325967149/625000000 : ℝ)] ![(11760650413987/100000000000000 : ℝ), (45318132318451/100000000000000 : ℝ), (21460608627963/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3008827/15625000 : ℝ)|^4445 ≤ (11760650413987/100000000000000 : ℝ)^3421
        have hw : |(-3008827/15625000 : ℝ)|=(3008827/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(543822329/1000000000 : ℝ)|^4445 ≤ (45318132318451/100000000000000 : ℝ)^3421
        have hw : |(543822329/1000000000 : ℝ)|=(543822329/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(325967149/625000000 : ℝ)|^4445 ≤ (21460608627963/50000000000000 : ℝ)^3421
        have hw : |(325967149/625000000 : ℝ)|=(325967149/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s6_1 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353617019/10000000000 : ℝ)*x 0 + (-2039821931/10000000000 : ℝ)*x 1 + (5215474387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353617019/10000000000 : ℝ)^4445 ≤ (5550523403647/12500000000000 : ℝ)^3421 := by
    have hnat : (5353617019 : ℕ)^4445*12500000000000^3421 ≤ 5550523403647^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353617019 10000000000 5550523403647 12500000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2039821931/10000000000 : ℝ)^4445 ≤ (633729773999/5000000000000 : ℝ)^3421 := by
    have hnat : (2039821931 : ℕ)^4445*5000000000000^3421 ≤ 633729773999^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2039821931 10000000000 633729773999 5000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215474387/10000000000 : ℝ)^4445 ≤ (8584243457601/20000000000000 : ℝ)^3421 := by
    have hnat : (5215474387 : ℕ)^4445*20000000000000^3421 ≤ 8584243457601^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215474387 10000000000 8584243457601 20000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353617019/10000000000 : ℝ), (-2039821931/10000000000 : ℝ), (5215474387/10000000000 : ℝ)] ![(5550523403647/12500000000000 : ℝ), (633729773999/5000000000000 : ℝ), (8584243457601/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353617019/10000000000 : ℝ)|^4445 ≤ (5550523403647/12500000000000 : ℝ)^3421
        have hw : |(5353617019/10000000000 : ℝ)|=(5353617019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2039821931/10000000000 : ℝ)|^4445 ≤ (633729773999/5000000000000 : ℝ)^3421
        have hw : |(-2039821931/10000000000 : ℝ)|=(2039821931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215474387/10000000000 : ℝ)|^4445 ≤ (8584243457601/20000000000000 : ℝ)^3421
        have hw : |(5215474387/10000000000 : ℝ)|=(5215474387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s6_2 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070723427/2000000000 : ℝ)*x 0 + (5215474401/10000000000 : ℝ)*x 1 + (-509955439/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070723427/2000000000 : ℝ)^4445 ≤ (44404188479301/100000000000000 : ℝ)^3421 := by
    have hnat : (1070723427 : ℕ)^4445*100000000000000^3421 ≤ 44404188479301^3421*2000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070723427 2000000000 44404188479301 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5215474401/10000000000 : ℝ)^4445 ≤ (21460608718853/50000000000000 : ℝ)^3421 := by
    have hnat : (5215474401 : ℕ)^4445*50000000000000^3421 ≤ 21460608718853^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215474401 10000000000 21460608718853 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (509955439/2500000000 : ℝ)^4445 ≤ (6337297033561/50000000000000 : ℝ)^3421 := by
    have hnat : (509955439 : ℕ)^4445*50000000000000^3421 ≤ 6337297033561^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509955439 2500000000 6337297033561 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070723427/2000000000 : ℝ), (5215474401/10000000000 : ℝ), (-509955439/2500000000 : ℝ)] ![(44404188479301/100000000000000 : ℝ), (21460608718853/50000000000000 : ℝ), (6337297033561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070723427/2000000000 : ℝ)|^4445 ≤ (44404188479301/100000000000000 : ℝ)^3421
        have hw : |(1070723427/2000000000 : ℝ)|=(1070723427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5215474401/10000000000 : ℝ)|^4445 ≤ (21460608718853/50000000000000 : ℝ)^3421
        have hw : |(5215474401/10000000000 : ℝ)|=(5215474401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-509955439/2500000000 : ℝ)|^4445 ≤ (6337297033561/50000000000000 : ℝ)^3421
        have hw : |(-509955439/2500000000 : ℝ)|=(509955439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s6_3 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (428780269/1000000000 : ℝ)*x 0 + (506021899/1250000000 : ℝ)*x 1 + (1134945511/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428780269/1000000000 : ℝ)^4445 ≤ (2079852337649/6250000000000 : ℝ)^3421 := by
    have hnat : (428780269 : ℕ)^4445*6250000000000^3421 ≤ 2079852337649^3421*1000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428780269 1000000000 2079852337649 6250000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (506021899/1250000000 : ℝ)^4445 ≤ (1544084771711/5000000000000 : ℝ)^3421 := by
    have hnat : (506021899 : ℕ)^4445*5000000000000^3421 ≤ 1544084771711^3421*1250000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506021899 1250000000 1544084771711 5000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1134945511/2500000000 : ℝ)^4445 ≤ (7168133429971/20000000000000 : ℝ)^3421 := by
    have hnat : (1134945511 : ℕ)^4445*20000000000000^3421 ≤ 7168133429971^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134945511 2500000000 7168133429971 20000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(428780269/1000000000 : ℝ), (506021899/1250000000 : ℝ), (1134945511/2500000000 : ℝ)] ![(2079852337649/6250000000000 : ℝ), (1544084771711/5000000000000 : ℝ), (7168133429971/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(428780269/1000000000 : ℝ)|^4445 ≤ (2079852337649/6250000000000 : ℝ)^3421
        have hw : |(428780269/1000000000 : ℝ)|=(428780269/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(506021899/1250000000 : ℝ)|^4445 ≤ (1544084771711/5000000000000 : ℝ)^3421
        have hw : |(506021899/1250000000 : ℝ)|=(506021899/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1134945511/2500000000 : ℝ)|^4445 ≤ (7168133429971/20000000000000 : ℝ)^3421
        have hw : |(1134945511/2500000000 : ℝ)|=(1134945511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s6_4 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-120354987/625000000 : ℝ)*x 0 + (5216612691/10000000000 : ℝ)*x 1 + (5437076709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (120354987/625000000 : ℝ)^4445 ≤ (5880446270863/50000000000000 : ℝ)^3421 := by
    have hnat : (120354987 : ℕ)^4445*50000000000000^3421 ≤ 5880446270863^3421*625000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120354987 625000000 5880446270863 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216612691/10000000000 : ℝ)^4445 ≤ (10733347373909/25000000000000 : ℝ)^3421 := by
    have hnat : (5216612691 : ℕ)^4445*25000000000000^3421 ≤ 10733347373909^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216612691 10000000000 10733347373909 25000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437076709/10000000000 : ℝ)^4445 ≤ (45305717948177/100000000000000 : ℝ)^3421 := by
    have hnat : (5437076709 : ℕ)^4445*100000000000000^3421 ≤ 45305717948177^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437076709 10000000000 45305717948177 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-120354987/625000000 : ℝ), (5216612691/10000000000 : ℝ), (5437076709/10000000000 : ℝ)] ![(5880446270863/50000000000000 : ℝ), (10733347373909/25000000000000 : ℝ), (45305717948177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-120354987/625000000 : ℝ)|^4445 ≤ (5880446270863/50000000000000 : ℝ)^3421
        have hw : |(-120354987/625000000 : ℝ)|=(120354987/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216612691/10000000000 : ℝ)|^4445 ≤ (10733347373909/25000000000000 : ℝ)^3421
        have hw : |(5216612691/10000000000 : ℝ)|=(5216612691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437076709/10000000000 : ℝ)|^4445 ≤ (45305717948177/100000000000000 : ℝ)^3421
        have hw : |(5437076709/10000000000 : ℝ)|=(5437076709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s6_5 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059100737/2000000000 : ℝ)*x 0 + (-454554911/2500000000 : ℝ)*x 1 + (5437076709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059100737/2000000000 : ℝ)^4445 ≤ (10944730894791/25000000000000 : ℝ)^3421 := by
    have hnat : (1059100737 : ℕ)^4445*25000000000000^3421 ≤ 10944730894791^3421*2000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059100737 2000000000 10944730894791 25000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (454554911/2500000000 : ℝ)^4445 ≤ (10915358456197/100000000000000 : ℝ)^3421 := by
    have hnat : (454554911 : ℕ)^4445*100000000000000^3421 ≤ 10915358456197^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454554911 2500000000 10915358456197 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437076709/10000000000 : ℝ)^4445 ≤ (45305717948177/100000000000000 : ℝ)^3421 := by
    have hnat : (5437076709 : ℕ)^4445*100000000000000^3421 ≤ 45305717948177^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437076709 10000000000 45305717948177 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059100737/2000000000 : ℝ), (-454554911/2500000000 : ℝ), (5437076709/10000000000 : ℝ)] ![(10944730894791/25000000000000 : ℝ), (10915358456197/100000000000000 : ℝ), (45305717948177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059100737/2000000000 : ℝ)|^4445 ≤ (10944730894791/25000000000000 : ℝ)^3421
        have hw : |(1059100737/2000000000 : ℝ)|=(1059100737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-454554911/2500000000 : ℝ)|^4445 ≤ (10915358456197/100000000000000 : ℝ)^3421
        have hw : |(-454554911/2500000000 : ℝ)|=(454554911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437076709/10000000000 : ℝ)|^4445 ≤ (45305717948177/100000000000000 : ℝ)^3421
        have hw : |(5437076709/10000000000 : ℝ)|=(5437076709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s6_6 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059100737/2000000000 : ℝ)*x 0 + (5437076709/10000000000 : ℝ)*x 1 + (-454554911/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059100737/2000000000 : ℝ)^4445 ≤ (10944730894791/25000000000000 : ℝ)^3421 := by
    have hnat : (1059100737 : ℕ)^4445*25000000000000^3421 ≤ 10944730894791^3421*2000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059100737 2000000000 10944730894791 25000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437076709/10000000000 : ℝ)^4445 ≤ (45305717948177/100000000000000 : ℝ)^3421 := by
    have hnat : (5437076709 : ℕ)^4445*100000000000000^3421 ≤ 45305717948177^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437076709 10000000000 45305717948177 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (454554911/2500000000 : ℝ)^4445 ≤ (10915358456197/100000000000000 : ℝ)^3421 := by
    have hnat : (454554911 : ℕ)^4445*100000000000000^3421 ≤ 10915358456197^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454554911 2500000000 10915358456197 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059100737/2000000000 : ℝ), (5437076709/10000000000 : ℝ), (-454554911/2500000000 : ℝ)] ![(10944730894791/25000000000000 : ℝ), (45305717948177/100000000000000 : ℝ), (10915358456197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059100737/2000000000 : ℝ)|^4445 ≤ (10944730894791/25000000000000 : ℝ)^3421
        have hw : |(1059100737/2000000000 : ℝ)|=(1059100737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437076709/10000000000 : ℝ)|^4445 ≤ (45305717948177/100000000000000 : ℝ)^3421
        have hw : |(5437076709/10000000000 : ℝ)|=(5437076709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-454554911/2500000000 : ℝ)|^4445 ≤ (10915358456197/100000000000000 : ℝ)^3421
        have hw : |(-454554911/2500000000 : ℝ)|=(454554911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_s6_7 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4287870323/10000000000 : ℝ)*x 0 + (4537270027/10000000000 : ℝ)*x 1 + (506338203/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4287870323/10000000000 : ℝ)^4445 ≤ (519973740949/1562500000000 : ℝ)^3421 := by
    have hnat : (4287870323 : ℕ)^4445*1562500000000^3421 ≤ 519973740949^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4287870323 10000000000 519973740949 1562500000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4537270027/10000000000 : ℝ)^4445 ≤ (35814901187033/100000000000000 : ℝ)^3421 := by
    have hnat : (4537270027 : ℕ)^4445*100000000000000^3421 ≤ 35814901187033^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4537270027 10000000000 35814901187033 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (506338203/1250000000 : ℝ)^4445 ≤ (1545338968903/5000000000000 : ℝ)^3421 := by
    have hnat : (506338203 : ℕ)^4445*5000000000000^3421 ≤ 1545338968903^3421*1250000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506338203 1250000000 1545338968903 5000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4287870323/10000000000 : ℝ), (4537270027/10000000000 : ℝ), (506338203/1250000000 : ℝ)] ![(519973740949/1562500000000 : ℝ), (35814901187033/100000000000000 : ℝ), (1545338968903/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4287870323/10000000000 : ℝ)|^4445 ≤ (519973740949/1562500000000 : ℝ)^3421
        have hw : |(4287870323/10000000000 : ℝ)|=(4287870323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4537270027/10000000000 : ℝ)|^4445 ≤ (35814901187033/100000000000000 : ℝ)^3421
        have hw : |(4537270027/10000000000 : ℝ)|=(4537270027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(506338203/1250000000 : ℝ)|^4445 ≤ (1545338968903/5000000000000 : ℝ)^3421
        have hw : |(506338203/1250000000 : ℝ)|=(506338203/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1474_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20043759/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10759/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (269/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7737/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3869/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10759/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3869/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10759/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3869/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10759/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3869/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10759/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3869/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10759/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3869/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10759/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10759/100000 : ℝ) ^ (4443/1024 : ℝ) ≤ (786858992593571/12500000000000000000 : ℝ) := by
    have hpowers : (10759/100000 : ℝ)^4443 ≤ (786858992593571/12500000000000000000 : ℝ)^1024 := by
      have hnat : (10759 : ℕ)^4443*12500000000000000000^1024 ≤ 786858992593571^1024*100000^4443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10759 100000 786858992593571 12500000000000000000 4443 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10759/100000 : ℝ)) (X := (786858992593571/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3869/25000 : ℝ) ^ (4443/1024 : ℝ) ≤ (7620383408001419/25000000000000000000 : ℝ) := by
    have hpowers : (3869/25000 : ℝ)^4443 ≤ (7620383408001419/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3869 : ℕ)^4443*25000000000000000000^1024 ≤ 7620383408001419^1024*25000^4443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3869 25000 7620383408001419 25000000000000000000 4443 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3869/25000 : ℝ)) (X := (7620383408001419/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250786858992593571/6250000000000000000 : ℝ) ≤ (10000290147947097/10000000000000000 : ℝ) ^ (4443/1024 : ℝ) := by
    have hpowers : (6250786858992593571/6250000000000000000 : ℝ)^1024 ≤ (10000290147947097/10000000000000000 : ℝ)^4443 := by
      have hnat : (6250786858992593571 : ℕ)^1024*10000000000000000^4443 ≤ 10000290147947097^4443*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250786858992593571 6250000000000000000 10000290147947097 10000000000000000 1024 4443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000290147947097/10000000000000000 : ℝ)) (X := (6250786858992593571/6250000000000000000 : ℝ)) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25009194101393188561/25000000000000000000 : ℝ) ≤ (10000847483944159/10000000000000000 : ℝ) ^ (4443/1024 : ℝ) := by
    have hpowers : (25009194101393188561/25000000000000000000 : ℝ)^1024 ≤ (10000847483944159/10000000000000000 : ℝ)^4443 := by
      have hnat : (25009194101393188561 : ℕ)^1024*10000000000000000^4443 ≤ 10000847483944159^4443*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009194101393188561 25000000000000000000 10000847483944159 10000000000000000 1024 4443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000847483944159/10000000000000000 : ℝ)) (X := (25009194101393188561/25000000000000000000 : ℝ)) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507620383408001419/12500000000000000000 : ℝ) ≤ (10001404819941221/10000000000000000 : ℝ) ^ (4443/1024 : ℝ) := by
    have hpowers : (12507620383408001419/12500000000000000000 : ℝ)^1024 ≤ (10001404819941221/10000000000000000 : ℝ)^4443 := by
      have hnat : (12507620383408001419 : ℕ)^1024*10000000000000000^4443 ≤ 10001404819941221^4443*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507620383408001419 12500000000000000000 10001404819941221 10000000000000000 1024 4443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001404819941221/10000000000000000 : ℝ)) (X := (12507620383408001419/12500000000000000000 : ℝ)) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(786858992593571/12500000000000000000 : ℝ) ≤ ((889799544752484461/890000000000000000 : ℝ)+2*(278667998531/235850000000000 : ℝ)*(10759/100000 : ℝ))^(4443/1024 : ℝ) := by
    rw [show (889799544752484461/890000000000000000 : ℝ)+2*(278667998531/235850000000000 : ℝ)*(10759/100000 : ℝ)=(10000290147947097/10000000000000000 : ℝ) by norm_num, show 1+2*(786858992593571/12500000000000000000 : ℝ)=(6250786858992593571/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7620383408001419/25000000000000000000 : ℝ)+(786858992593571/12500000000000000000 : ℝ) ≤ ((889799544752484461/890000000000000000 : ℝ)+(278667998531/235850000000000 : ℝ)*((3869/25000 : ℝ)+(10759/100000 : ℝ)))^(4443/1024 : ℝ) := by
    rw [show (889799544752484461/890000000000000000 : ℝ)+(278667998531/235850000000000 : ℝ)*((3869/25000 : ℝ)+(10759/100000 : ℝ))=(10000847483944159/10000000000000000 : ℝ) by norm_num, show 1+(7620383408001419/25000000000000000000 : ℝ)+(786858992593571/12500000000000000000 : ℝ)=(25009194101393188561/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7620383408001419/25000000000000000000 : ℝ) ≤ ((889799544752484461/890000000000000000 : ℝ)+2*(278667998531/235850000000000 : ℝ)*(3869/25000 : ℝ))^(4443/1024 : ℝ) := by
    rw [show (889799544752484461/890000000000000000 : ℝ)+2*(278667998531/235850000000000 : ℝ)*(3869/25000 : ℝ)=(10001404819941221/10000000000000000 : ℝ) by norm_num, show 1+2*(7620383408001419/25000000000000000000 : ℝ)=(12507620383408001419/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (889799544752484461/890000000000000000 : ℝ)*(X 1 0+X 2 0)+(278667998531/235850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4443/1024 : ℝ)) (lo := (10759/100000 : ℝ)) (hi := (3869/25000 : ℝ)) (c := (889799544752484461/890000000000000000 : ℝ)) (alpha := (278667998531/235850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (889799544752484461/890000000000000000 : ℝ)*(X 0 1+X 2 1)+(278667998531/235850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4443/1024 : ℝ)) (lo := (10759/100000 : ℝ)) (hi := (3869/25000 : ℝ)) (c := (889799544752484461/890000000000000000 : ℝ)) (alpha := (278667998531/235850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (889799544752484461/890000000000000000 : ℝ)*(X 0 2+X 1 2)+(278667998531/235850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4443/1024 : ℝ)) (lo := (10759/100000 : ℝ)) (hi := (3869/25000 : ℝ)) (c := (889799544752484461/890000000000000000 : ℝ)) (alpha := (278667998531/235850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-3008827/15625000 : ℝ)*X 0 0+(543822329/1000000000 : ℝ)*X 0 1+(325967149/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353617019/10000000000 : ℝ)*X 1 0+(-2039821931/10000000000 : ℝ)*X 1 1+(5215474387/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070723427/2000000000 : ℝ)*X 2 0+(5215474401/10000000000 : ℝ)*X 2 1+(-509955439/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((428780269/1000000000 : ℝ)*X 0 0+(506021899/1250000000 : ℝ)*X 0 1+(1134945511/2500000000 : ℝ)*X 0 2+(428780269/1000000000 : ℝ)*X 1 0+(506021899/1250000000 : ℝ)*X 1 1+(1134945511/2500000000 : ℝ)*X 1 2+(428780269/1000000000 : ℝ)*X 2 0+(506021899/1250000000 : ℝ)*X 2 1+(1134945511/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-120354987/625000000 : ℝ)*X 0 0+(5216612691/10000000000 : ℝ)*X 0 1+(5437076709/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1059100737/2000000000 : ℝ)*X 1 0+(-454554911/2500000000 : ℝ)*X 1 1+(5437076709/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1059100737/2000000000 : ℝ)*X 2 0+(5437076709/10000000000 : ℝ)*X 2 1+(-454554911/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4287870323/10000000000 : ℝ)*X 0 0+(4537270027/10000000000 : ℝ)*X 0 1+(506338203/1250000000 : ℝ)*X 0 2+(4287870323/10000000000 : ℝ)*X 1 0+(4537270027/10000000000 : ℝ)*X 1 1+(506338203/1250000000 : ℝ)*X 1 2+(4287870323/10000000000 : ℝ)*X 2 0+(4537270027/10000000000 : ℝ)*X 2 1+(506338203/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (369678113385855615795081603/44500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (848426479/50000000000000 : ℝ)*(base19) + (891366779/50000000000000 : ℝ)*(base23) + (108334851/100000000000000 : ℝ)*(upper3) + (6100039/100000000000000 : ℝ)*(upper4) + (279176161/100000000000000 : ℝ)*(upper5) + (3261794350155447/100000000000000 : ℝ)*(major0) + (3261794350155447/100000000000000 : ℝ)*(major1) + (3261794350155447/100000000000000 : ℝ)*(major2) + (224469290521547/5000000000000 : ℝ)*(sp0) + (2244707960855383/50000000000000 : ℝ)*(sp1) + (897883167166033/20000000000000 : ℝ)*(sp2) + (2034158988692247/100000000000000 : ℝ)*(sp3) + (1988008299/6250000000000 : ℝ)*(sp4) + (11816142469/100000000000000 : ℝ)*(sp7) + (508542701208679/25000000000000 : ℝ)*(f.failure) + (1122354404640931/25000000000000 : ℝ)*(f.sum) + (94302408993149/23585000000000000000000000000 : ℝ)*base65 + (32786718297849119449/4717000000000000000000000000000000 : ℝ)*base68 + (54507370788602119449/4717000000000000000000000000000000 : ℝ)*base70 + (43346906953529119449/4717000000000000000000000000000000 : ℝ)*base72 + (77169412348229/23585000000000000000000000000 : ℝ)*base73 + (68933756918444119449/4717000000000000000000000000000000 : ℝ)*base76 + (42595728104486119449/4717000000000000000000000000000000 : ℝ)*base78 + (1036364037506119449/4717000000000000000000000000000000 : ℝ)*base80 + (67003630663037/11792500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1290639/312500000000000000000 : ℝ)*base90 + (1290639/312500000000000000000 : ℝ)*base92 + (1290639/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (94575957237204862570167/11792500000000000000000000000 : ℝ) := by norm_num
    linear_combination (167115473/12500000000000 : ℝ)*(base19) + (1451148951/100000000000000 : ℝ)*(base23) + (111192959/25000000000000 : ℝ)*(lower1) + (16525623/10000000000000 : ℝ)*(upper3) + (51670849/100000000000000 : ℝ)*(lower4) + (165357097/100000000000000 : ℝ)*(upper5) + (3295541906624149/100000000000000 : ℝ)*(major0) + (3295541906624149/100000000000000 : ℝ)*(major1) + (3295541906624149/100000000000000 : ℝ)*(major2) + (303445487/20000000000000 : ℝ)*(sp2) + (226793328313259/5000000000000 : ℝ)*(sp4) + (907173045868279/20000000000000 : ℝ)*(sp5) + (4535863597888793/100000000000000 : ℝ)*(sp6) + (2055216979649469/100000000000000 : ℝ)*(sp7) + (2055216979649469/100000000000000 : ℝ)*(f.failure) + (226793328313259/5000000000000 : ℝ)*(f.sum) + (139866674861943/23585000000000000000000000000 : ℝ)*base65 + (160658988905045219483/4717000000000000000000000000000000 : ℝ)*base68 + (30813852701106219483/4717000000000000000000000000000000 : ℝ)*base70 + (97860045077331780517/4717000000000000000000000000000000 : ℝ)*base71 + (50233999594317/23585000000000000000000000000 : ℝ)*base74 + (63211984345001219483/4717000000000000000000000000000000 : ℝ)*base76 + (13358478982796780517/4717000000000000000000000000000000 : ℝ)*base77 + (50330466879590780517/4717000000000000000000000000000000 : ℝ)*base79 + (42392845091301/11792500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1386029/1250000000000000000000 : ℝ)*base90 + (1386029/1250000000000000000000 : ℝ)*base92 + (1386029/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1474_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20043759/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10759/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (269/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1474_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1474_box_0 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-170496261/1000000000 : ℝ)*x 0 + (5406955153/10000000000 : ℝ)*x 1 + (5406954353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (170496261/1000000000 : ℝ)^4445 ≤ (5020140284629/50000000000000 : ℝ)^3421 := by
    have hnat : (170496261 : ℕ)^4445*50000000000000^3421 ≤ 5020140284629^3421*1000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      170496261 1000000000 5020140284629 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406955153/10000000000 : ℝ)^4445 ≤ (5622483004273/12500000000000 : ℝ)^3421 := by
    have hnat : (5406955153 : ℕ)^4445*12500000000000^3421 ≤ 5622483004273^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406955153 10000000000 5622483004273 12500000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406954353/10000000000 : ℝ)^4445 ≤ (22489927693507/50000000000000 : ℝ)^3421 := by
    have hnat : (5406954353 : ℕ)^4445*50000000000000^3421 ≤ 22489927693507^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406954353 10000000000 22489927693507 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-170496261/1000000000 : ℝ), (5406955153/10000000000 : ℝ), (5406954353/10000000000 : ℝ)] ![(5020140284629/50000000000000 : ℝ), (5622483004273/12500000000000 : ℝ), (22489927693507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-170496261/1000000000 : ℝ)|^4445 ≤ (5020140284629/50000000000000 : ℝ)^3421
        have hw : |(-170496261/1000000000 : ℝ)|=(170496261/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406955153/10000000000 : ℝ)|^4445 ≤ (5622483004273/12500000000000 : ℝ)^3421
        have hw : |(5406955153/10000000000 : ℝ)|=(5406955153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406954353/10000000000 : ℝ)|^4445 ≤ (22489927693507/50000000000000 : ℝ)^3421
        have hw : |(5406954353/10000000000 : ℝ)|=(5406954353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_box_1 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270098761/10000000000 : ℝ)*x 0 + (-75779231/400000000 : ℝ)*x 1 + (1351738683/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270098761/10000000000 : ℝ)^4445 ≤ (21753112740961/50000000000000 : ℝ)^3421 := by
    have hnat : (5270098761 : ℕ)^4445*50000000000000^3421 ≤ 21753112740961^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270098761 10000000000 21753112740961 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (75779231/400000000 : ℝ)^4445 ≤ (5756957507343/50000000000000 : ℝ)^3421 := by
    have hnat : (75779231 : ℕ)^4445*50000000000000^3421 ≤ 5756957507343^3421*400000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75779231 400000000 5756957507343 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351738683/2500000000 : ℝ)^4445 ≤ (44979859483611/100000000000000 : ℝ)^3421 := by
    have hnat : (1351738683 : ℕ)^4445*100000000000000^3421 ≤ 44979859483611^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351738683 2500000000 44979859483611 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270098761/10000000000 : ℝ), (-75779231/400000000 : ℝ), (1351738683/2500000000 : ℝ)] ![(21753112740961/50000000000000 : ℝ), (5756957507343/50000000000000 : ℝ), (44979859483611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270098761/10000000000 : ℝ)|^4445 ≤ (21753112740961/50000000000000 : ℝ)^3421
        have hw : |(5270098761/10000000000 : ℝ)|=(5270098761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-75779231/400000000 : ℝ)|^4445 ≤ (5756957507343/50000000000000 : ℝ)^3421
        have hw : |(-75779231/400000000 : ℝ)|=(75779231/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351738683/2500000000 : ℝ)|^4445 ≤ (44979859483611/100000000000000 : ℝ)^3421
        have hw : |(1351738683/2500000000 : ℝ)|=(1351738683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_box_2 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270099559/10000000000 : ℝ)*x 0 + (1351738467/2500000000 : ℝ)*x 1 + (-947240437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270099559/10000000000 : ℝ)^4445 ≤ (43506234041537/100000000000000 : ℝ)^3421 := by
    have hnat : (5270099559 : ℕ)^4445*100000000000000^3421 ≤ 43506234041537^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270099559 10000000000 43506234041537 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351738467/2500000000 : ℝ)^4445 ≤ (22489925072333/50000000000000 : ℝ)^3421 := by
    have hnat : (1351738467 : ℕ)^4445*50000000000000^3421 ≤ 22489925072333^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351738467 2500000000 22489925072333 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (947240437/5000000000 : ℝ)^4445 ≤ (1151391579647/10000000000000 : ℝ)^3421 := by
    have hnat : (947240437 : ℕ)^4445*10000000000000^3421 ≤ 1151391579647^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947240437 5000000000 1151391579647 10000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270099559/10000000000 : ℝ), (1351738467/2500000000 : ℝ), (-947240437/5000000000 : ℝ)] ![(43506234041537/100000000000000 : ℝ), (22489925072333/50000000000000 : ℝ), (1151391579647/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270099559/10000000000 : ℝ)|^4445 ≤ (43506234041537/100000000000000 : ℝ)^3421
        have hw : |(5270099559/10000000000 : ℝ)|=(5270099559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351738467/2500000000 : ℝ)|^4445 ≤ (22489925072333/50000000000000 : ℝ)^3421
        have hw : |(1351738467/2500000000 : ℝ)|=(1351738467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-947240437/5000000000 : ℝ)|^4445 ≤ (1151391579647/10000000000000 : ℝ)^3421
        have hw : |(-947240437/5000000000 : ℝ)|=(947240437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_box_3 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2246358991/5000000000 : ℝ)*x 0 + (262036659/625000000 : ℝ)*x 1 + (2096293589/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2246358991/5000000000 : ℝ)^4445 ≤ (35358638137643/100000000000000 : ℝ)^3421 := by
    have hnat : (2246358991 : ℕ)^4445*100000000000000^3421 ≤ 35358638137643^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246358991 5000000000 35358638137643 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262036659/625000000 : ℝ)^4445 ≤ (32320677747329/100000000000000 : ℝ)^3421 := by
    have hnat : (262036659 : ℕ)^4445*100000000000000^3421 ≤ 32320677747329^3421*625000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262036659 625000000 32320677747329 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2096293589/5000000000 : ℝ)^4445 ≤ (32320684097807/100000000000000 : ℝ)^3421 := by
    have hnat : (2096293589 : ℕ)^4445*100000000000000^3421 ≤ 32320684097807^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096293589 5000000000 32320684097807 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2246358991/5000000000 : ℝ), (262036659/625000000 : ℝ), (2096293589/5000000000 : ℝ)] ![(35358638137643/100000000000000 : ℝ), (32320677747329/100000000000000 : ℝ), (32320684097807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2246358991/5000000000 : ℝ)|^4445 ≤ (35358638137643/100000000000000 : ℝ)^3421
        have hw : |(2246358991/5000000000 : ℝ)|=(2246358991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262036659/625000000 : ℝ)|^4445 ≤ (32320677747329/100000000000000 : ℝ)^3421
        have hw : |(262036659/625000000 : ℝ)|=(262036659/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2096293589/5000000000 : ℝ)|^4445 ≤ (32320684097807/100000000000000 : ℝ)^3421
        have hw : |(2096293589/5000000000 : ℝ)|=(2096293589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_box_4 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2151811853/10000000000 : ℝ)*x 0 + (2621088153/5000000000 : ℝ)*x 1 + (1048435357/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151811853/10000000000 : ℝ)^4445 ≤ (6793039753329/50000000000000 : ℝ)^3421 := by
    have hnat : (2151811853 : ℕ)^4445*50000000000000^3421 ≤ 6793039753329^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151811853 10000000000 6793039753329 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621088153/5000000000 : ℝ)^4445 ≤ (10801739418817/25000000000000 : ℝ)^3421 := by
    have hnat : (2621088153 : ℕ)^4445*25000000000000^3421 ≤ 10801739418817^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621088153 5000000000 10801739418817 25000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048435357/2000000000 : ℝ)^4445 ≤ (43206962805019/100000000000000 : ℝ)^3421 := by
    have hnat : (1048435357 : ℕ)^4445*100000000000000^3421 ≤ 43206962805019^3421*2000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048435357 2000000000 43206962805019 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2151811853/10000000000 : ℝ), (2621088153/5000000000 : ℝ), (1048435357/2000000000 : ℝ)] ![(6793039753329/50000000000000 : ℝ), (10801739418817/25000000000000 : ℝ), (43206962805019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2151811853/10000000000 : ℝ)|^4445 ≤ (6793039753329/50000000000000 : ℝ)^3421
        have hw : |(-2151811853/10000000000 : ℝ)|=(2151811853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621088153/5000000000 : ℝ)|^4445 ≤ (10801739418817/25000000000000 : ℝ)^3421
        have hw : |(2621088153/5000000000 : ℝ)|=(2621088153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048435357/2000000000 : ℝ)|^4445 ≤ (43206962805019/100000000000000 : ℝ)^3421
        have hw : |(1048435357/2000000000 : ℝ)|=(1048435357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_box_5 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2692581651/5000000000 : ℝ)*x 0 + (-1961831557/10000000000 : ℝ)*x 1 + (209687073/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2692581651/5000000000 : ℝ)^4445 ≤ (44744458920887/100000000000000 : ℝ)^3421 := by
    have hnat : (2692581651 : ℕ)^4445*100000000000000^3421 ≤ 44744458920887^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692581651 5000000000 44744458920887 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1961831557/10000000000 : ℝ)^4445 ≤ (12048577824317/100000000000000 : ℝ)^3421 := by
    have hnat : (1961831557 : ℕ)^4445*100000000000000^3421 ≤ 12048577824317^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1961831557 10000000000 12048577824317 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209687073/400000000 : ℝ)^4445 ≤ (43206963233391/100000000000000 : ℝ)^3421 := by
    have hnat : (209687073 : ℕ)^4445*100000000000000^3421 ≤ 43206963233391^3421*400000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209687073 400000000 43206963233391 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2692581651/5000000000 : ℝ), (-1961831557/10000000000 : ℝ), (209687073/400000000 : ℝ)] ![(44744458920887/100000000000000 : ℝ), (12048577824317/100000000000000 : ℝ), (43206963233391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2692581651/5000000000 : ℝ)|^4445 ≤ (44744458920887/100000000000000 : ℝ)^3421
        have hw : |(2692581651/5000000000 : ℝ)|=(2692581651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1961831557/10000000000 : ℝ)|^4445 ≤ (12048577824317/100000000000000 : ℝ)^3421
        have hw : |(-1961831557/10000000000 : ℝ)|=(1961831557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209687073/400000000 : ℝ)|^4445 ≤ (43206963233391/100000000000000 : ℝ)^3421
        have hw : |(209687073/400000000 : ℝ)|=(209687073/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_box_6 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2692581907/5000000000 : ℝ)*x 0 + (5242176503/10000000000 : ℝ)*x 1 + (-980915649/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2692581907/5000000000 : ℝ)^4445 ≤ (44744464448391/100000000000000 : ℝ)^3421 := by
    have hnat : (2692581907 : ℕ)^4445*100000000000000^3421 ≤ 44744464448391^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692581907 5000000000 44744464448391 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242176503/10000000000 : ℝ)^4445 ≤ (43206959784999/100000000000000 : ℝ)^3421 := by
    have hnat : (5242176503 : ℕ)^4445*100000000000000^3421 ≤ 43206959784999^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242176503 10000000000 43206959784999 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (980915649/5000000000 : ℝ)^4445 ≤ (2409715151509/20000000000000 : ℝ)^3421 := by
    have hnat : (980915649 : ℕ)^4445*20000000000000^3421 ≤ 2409715151509^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980915649 5000000000 2409715151509 20000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2692581907/5000000000 : ℝ), (5242176503/10000000000 : ℝ), (-980915649/5000000000 : ℝ)] ![(44744464448391/100000000000000 : ℝ), (43206959784999/100000000000000 : ℝ), (2409715151509/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2692581907/5000000000 : ℝ)|^4445 ≤ (44744464448391/100000000000000 : ℝ)^3421
        have hw : |(2692581907/5000000000 : ℝ)|=(2692581907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242176503/10000000000 : ℝ)|^4445 ≤ (43206959784999/100000000000000 : ℝ)^3421
        have hw : |(5242176503/10000000000 : ℝ)|=(5242176503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-980915649/5000000000 : ℝ)|^4445 ≤ (2409715151509/20000000000000 : ℝ)^3421
        have hw : |(-980915649/5000000000 : ℝ)|=(980915649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_box_7 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1020165023/2500000000 : ℝ)*x 0 + (439847613/1000000000 : ℝ)*x 1 + (1099619099/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1020165023/2500000000 : ℝ)^4445 ≤ (15602035589573/50000000000000 : ℝ)^3421 := by
    have hnat : (1020165023 : ℕ)^4445*50000000000000^3421 ≤ 15602035589573^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1020165023 2500000000 15602035589573 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (439847613/1000000000 : ℝ)^4445 ≤ (17198981524159/50000000000000 : ℝ)^3421 := by
    have hnat : (439847613 : ℕ)^4445*50000000000000^3421 ≤ 17198981524159^3421*1000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439847613 1000000000 17198981524159 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1099619099/2500000000 : ℝ)^4445 ≤ (34397965751223/100000000000000 : ℝ)^3421 := by
    have hnat : (1099619099 : ℕ)^4445*100000000000000^3421 ≤ 34397965751223^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099619099 2500000000 34397965751223 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1020165023/2500000000 : ℝ), (439847613/1000000000 : ℝ), (1099619099/2500000000 : ℝ)] ![(15602035589573/50000000000000 : ℝ), (17198981524159/50000000000000 : ℝ), (34397965751223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1020165023/2500000000 : ℝ)|^4445 ≤ (15602035589573/50000000000000 : ℝ)^3421
        have hw : |(1020165023/2500000000 : ℝ)|=(1020165023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(439847613/1000000000 : ℝ)|^4445 ≤ (17198981524159/50000000000000 : ℝ)^3421
        have hw : |(439847613/1000000000 : ℝ)|=(439847613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1099619099/2500000000 : ℝ)|^4445 ≤ (34397965751223/100000000000000 : ℝ)^3421
        have hw : |(1099619099/2500000000 : ℝ)|=(1099619099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_box_8 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-411520797/2000000000 : ℝ)*x 0 + (5127172207/10000000000 : ℝ)*x 1 + (2713758591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (411520797/2000000000 : ℝ)^4445 ≤ (2563669077101/20000000000000 : ℝ)^3421 := by
    have hnat : (411520797 : ℕ)^4445*20000000000000^3421 ≤ 2563669077101^3421*2000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411520797 2000000000 2563669077101 20000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5127172207/10000000000 : ℝ)^4445 ≤ (2623713122171/6250000000000 : ℝ)^3421 := by
    have hnat : (5127172207 : ℕ)^4445*6250000000000^3421 ≤ 2623713122171^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5127172207 10000000000 2623713122171 6250000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713758591/5000000000 : ℝ)^4445 ≤ (45202244645919/100000000000000 : ℝ)^3421 := by
    have hnat : (2713758591 : ℕ)^4445*100000000000000^3421 ≤ 45202244645919^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713758591 5000000000 45202244645919 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-411520797/2000000000 : ℝ), (5127172207/10000000000 : ℝ), (2713758591/5000000000 : ℝ)] ![(2563669077101/20000000000000 : ℝ), (2623713122171/6250000000000 : ℝ), (45202244645919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-411520797/2000000000 : ℝ)|^4445 ≤ (2563669077101/20000000000000 : ℝ)^3421
        have hw : |(-411520797/2000000000 : ℝ)|=(411520797/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5127172207/10000000000 : ℝ)|^4445 ≤ (2623713122171/6250000000000 : ℝ)^3421
        have hw : |(5127172207/10000000000 : ℝ)|=(5127172207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713758591/5000000000 : ℝ)|^4445 ≤ (45202244645919/100000000000000 : ℝ)^3421
        have hw : |(2713758591/5000000000 : ℝ)|=(2713758591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_box_9 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (656966533/1250000000 : ℝ)*x 0 + (-942909817/5000000000 : ℝ)*x 1 + (5427517209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (656966533/1250000000 : ℝ)^4445 ≤ (21676094269063/50000000000000 : ℝ)^3421 := by
    have hnat : (656966533 : ℕ)^4445*50000000000000^3421 ≤ 21676094269063^3421*1250000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656966533 1250000000 21676094269063 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (942909817/5000000000 : ℝ)^4445 ≤ (11445566506461/100000000000000 : ℝ)^3421 := by
    have hnat : (942909817 : ℕ)^4445*100000000000000^3421 ≤ 11445566506461^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      942909817 5000000000 11445566506461 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427517209/10000000000 : ℝ)^4445 ≤ (45202244938093/100000000000000 : ℝ)^3421 := by
    have hnat : (5427517209 : ℕ)^4445*100000000000000^3421 ≤ 45202244938093^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427517209 10000000000 45202244938093 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(656966533/1250000000 : ℝ), (-942909817/5000000000 : ℝ), (5427517209/10000000000 : ℝ)] ![(21676094269063/50000000000000 : ℝ), (11445566506461/100000000000000 : ℝ), (45202244938093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(656966533/1250000000 : ℝ)|^4445 ≤ (21676094269063/50000000000000 : ℝ)^3421
        have hw : |(656966533/1250000000 : ℝ)|=(656966533/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-942909817/5000000000 : ℝ)|^4445 ≤ (11445566506461/100000000000000 : ℝ)^3421
        have hw : |(-942909817/5000000000 : ℝ)|=(942909817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427517209/10000000000 : ℝ)|^4445 ≤ (45202244938093/100000000000000 : ℝ)^3421
        have hw : |(5427517209/10000000000 : ℝ)|=(5427517209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_box_10 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525573279/1000000000 : ℝ)*x 0 + (5427516673/10000000000 : ℝ)*x 1 + (-942909827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525573279/1000000000 : ℝ)^4445 ≤ (43352194175569/100000000000000 : ℝ)^3421 := by
    have hnat : (525573279 : ℕ)^4445*100000000000000^3421 ≤ 43352194175569^3421*1000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525573279 1000000000 43352194175569 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427516673/10000000000 : ℝ)^4445 ≤ (22601119568951/50000000000000 : ℝ)^3421 := by
    have hnat : (5427516673 : ℕ)^4445*50000000000000^3421 ≤ 22601119568951^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427516673 10000000000 22601119568951 50000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (942909827/5000000000 : ℝ)^4445 ≤ (11445566664181/100000000000000 : ℝ)^3421 := by
    have hnat : (942909827 : ℕ)^4445*100000000000000^3421 ≤ 11445566664181^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      942909827 5000000000 11445566664181 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525573279/1000000000 : ℝ), (5427516673/10000000000 : ℝ), (-942909827/5000000000 : ℝ)] ![(43352194175569/100000000000000 : ℝ), (22601119568951/50000000000000 : ℝ), (11445566664181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525573279/1000000000 : ℝ)|^4445 ≤ (43352194175569/100000000000000 : ℝ)^3421
        have hw : |(525573279/1000000000 : ℝ)|=(525573279/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427516673/10000000000 : ℝ)|^4445 ≤ (22601119568951/50000000000000 : ℝ)^3421
        have hw : |(5427516673/10000000000 : ℝ)|=(5427516673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-942909827/5000000000 : ℝ)|^4445 ≤ (11445566664181/100000000000000 : ℝ)^3421
        have hw : |(-942909827/5000000000 : ℝ)|=(942909827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_box_11 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4542981911/10000000000 : ℝ)*x 0 + (4166862713/10000000000 : ℝ)*x 1 + (2083431497/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4542981911/10000000000 : ℝ)^4445 ≤ (35873494626809/100000000000000 : ℝ)^3421 := by
    have hnat : (4542981911 : ℕ)^4445*100000000000000^3421 ≤ 35873494626809^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4542981911 10000000000 35873494626809 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4166862713/10000000000 : ℝ)^4445 ≤ (6412650254993/20000000000000 : ℝ)^3421 := by
    have hnat : (4166862713 : ℕ)^4445*20000000000000^3421 ≤ 6412650254993^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4166862713 10000000000 6412650254993 20000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2083431497/5000000000 : ℝ)^4445 ≤ (8015813521107/25000000000000 : ℝ)^3421 := by
    have hnat : (2083431497 : ℕ)^4445*25000000000000^3421 ≤ 8015813521107^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2083431497 5000000000 8015813521107 25000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4542981911/10000000000 : ℝ), (4166862713/10000000000 : ℝ), (2083431497/5000000000 : ℝ)] ![(35873494626809/100000000000000 : ℝ), (6412650254993/20000000000000 : ℝ), (8015813521107/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4542981911/10000000000 : ℝ)|^4445 ≤ (35873494626809/100000000000000 : ℝ)^3421
        have hw : |(4542981911/10000000000 : ℝ)|=(4542981911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4166862713/10000000000 : ℝ)|^4445 ≤ (6412650254993/20000000000000 : ℝ)^3421
        have hw : |(4166862713/10000000000 : ℝ)|=(4166862713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2083431497/5000000000 : ℝ)|^4445 ≤ (8015813521107/25000000000000 : ℝ)^3421
        have hw : |(2083431497/5000000000 : ℝ)|=(2083431497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_box_12 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1799338011/10000000000 : ℝ)*x 0 + (5518121647/10000000000 : ℝ)*x 1 + (261359603/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1799338011/10000000000 : ℝ)^4445 ≤ (10768305844373/100000000000000 : ℝ)^3421 := by
    have hnat : (1799338011 : ℕ)^4445*100000000000000^3421 ≤ 10768305844373^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1799338011 10000000000 10768305844373 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5518121647/10000000000 : ℝ)^4445 ≤ (1847405537513/4000000000000 : ℝ)^3421 := by
    have hnat : (5518121647 : ℕ)^4445*4000000000000^3421 ≤ 1847405537513^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518121647 10000000000 1847405537513 4000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261359603/500000000 : ℝ)^4445 ≤ (43046555706351/100000000000000 : ℝ)^3421 := by
    have hnat : (261359603 : ℕ)^4445*100000000000000^3421 ≤ 43046555706351^3421*500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261359603 500000000 43046555706351 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1799338011/10000000000 : ℝ), (5518121647/10000000000 : ℝ), (261359603/500000000 : ℝ)] ![(10768305844373/100000000000000 : ℝ), (1847405537513/4000000000000 : ℝ), (43046555706351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1799338011/10000000000 : ℝ)|^4445 ≤ (10768305844373/100000000000000 : ℝ)^3421
        have hw : |(-1799338011/10000000000 : ℝ)|=(1799338011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5518121647/10000000000 : ℝ)|^4445 ≤ (1847405537513/4000000000000 : ℝ)^3421
        have hw : |(5518121647/10000000000 : ℝ)|=(5518121647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(261359603/500000000 : ℝ)|^4445 ≤ (43046555706351/100000000000000 : ℝ)^3421
        have hw : |(261359603/500000000 : ℝ)|=(261359603/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_box_13 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1348906457/2500000000 : ℝ)*x 0 + (-983885717/5000000000 : ℝ)*x 1 + (5227192217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1348906457/2500000000 : ℝ)^4445 ≤ (44857444191501/100000000000000 : ℝ)^3421 := by
    have hnat : (1348906457 : ℕ)^4445*100000000000000^3421 ≤ 44857444191501^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348906457 2500000000 44857444191501 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (983885717/5000000000 : ℝ)^4445 ≤ (12095998400543/100000000000000 : ℝ)^3421 := by
    have hnat : (983885717 : ℕ)^4445*100000000000000^3421 ≤ 12095998400543^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983885717 5000000000 12095998400543 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227192217/10000000000 : ℝ)^4445 ≤ (4304655738627/10000000000000 : ℝ)^3421 := by
    have hnat : (5227192217 : ℕ)^4445*10000000000000^3421 ≤ 4304655738627^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227192217 10000000000 4304655738627 10000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1348906457/2500000000 : ℝ), (-983885717/5000000000 : ℝ), (5227192217/10000000000 : ℝ)] ![(44857444191501/100000000000000 : ℝ), (12095998400543/100000000000000 : ℝ), (4304655738627/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1348906457/2500000000 : ℝ)|^4445 ≤ (44857444191501/100000000000000 : ℝ)^3421
        have hw : |(1348906457/2500000000 : ℝ)|=(1348906457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-983885717/5000000000 : ℝ)|^4445 ≤ (12095998400543/100000000000000 : ℝ)^3421
        have hw : |(-983885717/5000000000 : ℝ)|=(983885717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227192217/10000000000 : ℝ)|^4445 ≤ (4304655738627/10000000000000 : ℝ)^3421
        have hw : |(5227192217/10000000000 : ℝ)|=(5227192217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_box_14 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1079125137/2000000000 : ℝ)*x 0 + (1306798017/2500000000 : ℝ)*x 1 + (-1967771829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1079125137/2000000000 : ℝ)^4445 ≤ (4485744264679/10000000000000 : ℝ)^3421 := by
    have hnat : (1079125137 : ℕ)^4445*10000000000000^3421 ≤ 4485744264679^3421*2000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079125137 2000000000 4485744264679 10000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1306798017/2500000000 : ℝ)^4445 ≤ (2690409736997/6250000000000 : ℝ)^3421 := by
    have hnat : (1306798017 : ℕ)^4445*6250000000000^3421 ≤ 2690409736997^3421*2500000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1306798017 2500000000 2690409736997 6250000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1967771829/10000000000 : ℝ)^4445 ≤ (12096001555423/100000000000000 : ℝ)^3421 := by
    have hnat : (1967771829 : ℕ)^4445*100000000000000^3421 ≤ 12096001555423^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1967771829 10000000000 12096001555423 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1079125137/2000000000 : ℝ), (1306798017/2500000000 : ℝ), (-1967771829/10000000000 : ℝ)] ![(4485744264679/10000000000000 : ℝ), (2690409736997/6250000000000 : ℝ), (12096001555423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1079125137/2000000000 : ℝ)|^4445 ≤ (4485744264679/10000000000000 : ℝ)^3421
        have hw : |(1079125137/2000000000 : ℝ)|=(1079125137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1306798017/2500000000 : ℝ)|^4445 ≤ (2690409736997/6250000000000 : ℝ)^3421
        have hw : |(1306798017/2500000000 : ℝ)|=(1306798017/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1967771829/10000000000 : ℝ)|^4445 ≤ (12096001555423/100000000000000 : ℝ)^3421
        have hw : |(-1967771829/10000000000 : ℝ)|=(1967771829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1474_box_15 (p : ℝ) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4042328039/10000000000 : ℝ)*x 0 + (2208589053/5000000000 : ℝ)*x 1 + (4417178939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4042328039/10000000000 : ℝ)^4445 ≤ (30823751088847/100000000000000 : ℝ)^3421 := by
    have hnat : (4042328039 : ℕ)^4445*100000000000000^3421 ≤ 30823751088847^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4042328039 10000000000 30823751088847 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2208589053/5000000000 : ℝ)^4445 ≤ (34588120206369/100000000000000 : ℝ)^3421 := by
    have hnat : (2208589053 : ℕ)^4445*100000000000000^3421 ≤ 34588120206369^3421*5000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208589053 5000000000 34588120206369 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4417178939/10000000000 : ℝ)^4445 ≤ (34588128681487/100000000000000 : ℝ)^3421 := by
    have hnat : (4417178939 : ℕ)^4445*100000000000000^3421 ≤ 34588128681487^3421*10000000000^4445 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4417178939 10000000000 34588128681487 100000000000000 4445 3421 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4445/1024 : ℝ)) 4445 3421 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4042328039/10000000000 : ℝ), (2208589053/5000000000 : ℝ), (4417178939/10000000000 : ℝ)] ![(30823751088847/100000000000000 : ℝ), (34588120206369/100000000000000 : ℝ), (34588128681487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4042328039/10000000000 : ℝ)|^4445 ≤ (30823751088847/100000000000000 : ℝ)^3421
        have hw : |(4042328039/10000000000 : ℝ)|=(4042328039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2208589053/5000000000 : ℝ)|^4445 ≤ (34588120206369/100000000000000 : ℝ)^3421
        have hw : |(2208589053/5000000000 : ℝ)|=(2208589053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4417178939/10000000000 : ℝ)|^4445 ≤ (34588128681487/100000000000000 : ℝ)^3421
        have hw : |(4417178939/10000000000 : ℝ)|=(4417178939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1474_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20043759/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (269/2500 : ℝ)*pair X i i ≤ pair X i h) :
    -(3981/6250 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(1169/2000 : ℝ) ∧ (799/1000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42877/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7737/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (269/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7737/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (269/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7737/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (269/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7737/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (269/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7737/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (269/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7737/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (269/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (269/2500 : ℝ) ^ (4443/1024 : ℝ) ≤ (1574352729392363/25000000000000000000 : ℝ) := by
    have hpowers : (269/2500 : ℝ)^4443 ≤ (1574352729392363/25000000000000000000 : ℝ)^1024 := by
      have hnat : (269 : ℕ)^4443*25000000000000000000^1024 ≤ 1574352729392363^1024*2500^4443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        269 2500 1574352729392363 25000000000000000000 4443 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (269/2500 : ℝ)) (X := (1574352729392363/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7737/50000 : ℝ) ^ (4443/1024 : ℝ) ≤ (30464445651187541/100000000000000000000 : ℝ) := by
    have hpowers : (7737/50000 : ℝ)^4443 ≤ (30464445651187541/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7737 : ℕ)^4443*100000000000000000000^1024 ≤ 30464445651187541^1024*50000^4443 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7737 50000 30464445651187541 100000000000000000000 4443 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7737/50000 : ℝ)) (X := (30464445651187541/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501574352729392363/12500000000000000000 : ℝ) ≤ (5000145132484923/5000000000000000 : ℝ) ^ (4443/1024 : ℝ) := by
    have hpowers : (12501574352729392363/12500000000000000000 : ℝ)^1024 ≤ (5000145132484923/5000000000000000 : ℝ)^4443 := by
      have hnat : (12501574352729392363 : ℕ)^1024*5000000000000000^4443 ≤ 5000145132484923^4443*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501574352729392363 12500000000000000000 5000145132484923 5000000000000000 1024 4443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000145132484923/5000000000000000 : ℝ)) (X := (12501574352729392363/12500000000000000000 : ℝ)) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036761856568756993/100000000000000000000 : ℝ) ≤ (625052946795061/625000000000000 : ℝ) ^ (4443/1024 : ℝ) := by
    have hpowers : (100036761856568756993/100000000000000000000 : ℝ)^1024 ≤ (625052946795061/625000000000000 : ℝ)^4443 := by
      have hnat : (100036761856568756993 : ℕ)^1024*625000000000000^4443 ≤ 625052946795061^4443*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036761856568756993 100000000000000000000 625052946795061 625000000000000 1024 4443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625052946795061/625000000000000 : ℝ)) (X := (100036761856568756993/100000000000000000000 : ℝ)) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030464445651187541/50000000000000000000 : ℝ) ≤ (5000702016236053/5000000000000000 : ℝ) ^ (4443/1024 : ℝ) := by
    have hpowers : (50030464445651187541/50000000000000000000 : ℝ)^1024 ≤ (5000702016236053/5000000000000000 : ℝ)^4443 := by
      have hnat : (50030464445651187541 : ℕ)^1024*5000000000000000^4443 ≤ 5000702016236053^4443*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030464445651187541 50000000000000000000 5000702016236053 5000000000000000 1024 4443 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000702016236053/5000000000000000 : ℝ)) (X := (50030464445651187541/50000000000000000000 : ℝ)) (by norm_num) 4443 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1574352729392363/25000000000000000000 : ℝ) ≤ ((11782346042685884111/11785000000000000000 : ℝ)+2*(55688375113/47140000000000 : ℝ)*(269/2500 : ℝ))^(4443/1024 : ℝ) := by
    rw [show (11782346042685884111/11785000000000000000 : ℝ)+2*(55688375113/47140000000000 : ℝ)*(269/2500 : ℝ)=(5000145132484923/5000000000000000 : ℝ) by norm_num, show 1+2*(1574352729392363/25000000000000000000 : ℝ)=(12501574352729392363/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30464445651187541/100000000000000000000 : ℝ)+(1574352729392363/25000000000000000000 : ℝ) ≤ ((11782346042685884111/11785000000000000000 : ℝ)+(55688375113/47140000000000 : ℝ)*((7737/50000 : ℝ)+(269/2500 : ℝ)))^(4443/1024 : ℝ) := by
    rw [show (11782346042685884111/11785000000000000000 : ℝ)+(55688375113/47140000000000 : ℝ)*((7737/50000 : ℝ)+(269/2500 : ℝ))=(625052946795061/625000000000000 : ℝ) by norm_num, show 1+(30464445651187541/100000000000000000000 : ℝ)+(1574352729392363/25000000000000000000 : ℝ)=(100036761856568756993/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30464445651187541/100000000000000000000 : ℝ) ≤ ((11782346042685884111/11785000000000000000 : ℝ)+2*(55688375113/47140000000000 : ℝ)*(7737/50000 : ℝ))^(4443/1024 : ℝ) := by
    rw [show (11782346042685884111/11785000000000000000 : ℝ)+2*(55688375113/47140000000000 : ℝ)*(7737/50000 : ℝ)=(5000702016236053/5000000000000000 : ℝ) by norm_num, show 1+2*(30464445651187541/100000000000000000000 : ℝ)=(50030464445651187541/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11782346042685884111/11785000000000000000 : ℝ)*(X 1 0+X 2 0)+(55688375113/47140000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4443/1024 : ℝ)) (lo := (269/2500 : ℝ)) (hi := (7737/50000 : ℝ)) (c := (11782346042685884111/11785000000000000000 : ℝ)) (alpha := (55688375113/47140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11782346042685884111/11785000000000000000 : ℝ)*(X 0 1+X 2 1)+(55688375113/47140000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4443/1024 : ℝ)) (lo := (269/2500 : ℝ)) (hi := (7737/50000 : ℝ)) (c := (11782346042685884111/11785000000000000000 : ℝ)) (alpha := (55688375113/47140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11782346042685884111/11785000000000000000 : ℝ)*(X 0 2+X 1 2)+(55688375113/47140000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4443/1024 : ℝ)) (lo := (269/2500 : ℝ)) (hi := (7737/50000 : ℝ)) (c := (11782346042685884111/11785000000000000000 : ℝ)) (alpha := (55688375113/47140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-170496261/1000000000 : ℝ)*X 0 0+(5406955153/10000000000 : ℝ)*X 0 1+(5406954353/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5270098761/10000000000 : ℝ)*X 1 0+(-75779231/400000000 : ℝ)*X 1 1+(1351738683/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5270099559/10000000000 : ℝ)*X 2 0+(1351738467/2500000000 : ℝ)*X 2 1+(-947240437/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2246358991/5000000000 : ℝ)*X 0 0+(262036659/625000000 : ℝ)*X 0 1+(2096293589/5000000000 : ℝ)*X 0 2+(2246358991/5000000000 : ℝ)*X 1 0+(262036659/625000000 : ℝ)*X 1 1+(2096293589/5000000000 : ℝ)*X 1 2+(2246358991/5000000000 : ℝ)*X 2 0+(262036659/625000000 : ℝ)*X 2 1+(2096293589/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2151811853/10000000000 : ℝ)*X 0 0+(2621088153/5000000000 : ℝ)*X 0 1+(1048435357/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2692581651/5000000000 : ℝ)*X 1 0+(-1961831557/10000000000 : ℝ)*X 1 1+(209687073/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2692581907/5000000000 : ℝ)*X 2 0+(5242176503/10000000000 : ℝ)*X 2 1+(-980915649/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1020165023/2500000000 : ℝ)*X 0 0+(439847613/1000000000 : ℝ)*X 0 1+(1099619099/2500000000 : ℝ)*X 0 2+(1020165023/2500000000 : ℝ)*X 1 0+(439847613/1000000000 : ℝ)*X 1 1+(1099619099/2500000000 : ℝ)*X 1 2+(1020165023/2500000000 : ℝ)*X 2 0+(439847613/1000000000 : ℝ)*X 2 1+(1099619099/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-411520797/2000000000 : ℝ)*X 0 0+(5127172207/10000000000 : ℝ)*X 0 1+(2713758591/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((656966533/1250000000 : ℝ)*X 1 0+(-942909817/5000000000 : ℝ)*X 1 1+(5427517209/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((525573279/1000000000 : ℝ)*X 2 0+(5427516673/10000000000 : ℝ)*X 2 1+(-942909827/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4542981911/10000000000 : ℝ)*X 0 0+(4166862713/10000000000 : ℝ)*X 0 1+(2083431497/5000000000 : ℝ)*X 0 2+(4542981911/10000000000 : ℝ)*X 1 0+(4166862713/10000000000 : ℝ)*X 1 1+(2083431497/5000000000 : ℝ)*X 1 2+(4542981911/10000000000 : ℝ)*X 2 0+(4166862713/10000000000 : ℝ)*X 2 1+(2083431497/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1799338011/10000000000 : ℝ)*X 0 0+(5518121647/10000000000 : ℝ)*X 0 1+(261359603/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1348906457/2500000000 : ℝ)*X 1 0+(-983885717/5000000000 : ℝ)*X 1 1+(5227192217/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1079125137/2000000000 : ℝ)*X 2 0+(1306798017/2500000000 : ℝ)*X 2 1+(-1967771829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4042328039/10000000000 : ℝ)*X 0 0+(2208589053/5000000000 : ℝ)*X 0 1+(4417178939/10000000000 : ℝ)*X 0 2+(4042328039/10000000000 : ℝ)*X 1 0+(2208589053/5000000000 : ℝ)*X 1 1+(4417178939/10000000000 : ℝ)*X 1 2+(4042328039/10000000000 : ℝ)*X 2 0+(2208589053/5000000000 : ℝ)*X 2 1+(4417178939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1474_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-3981/6250 : ℝ) ≤ (-375315064020256844140146686484801/589250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1622457/100000000000000 : ℝ)*(lower1) + (16101279/20000000000000 : ℝ)*(lower2) + (33630731/25000000000000 : ℝ)*(lower3) + (19176747/100000000000000 : ℝ)*(upper5) + (2166623563875403/100000000000000 : ℝ)*(major0) + (2166623563875403/100000000000000 : ℝ)*(major1) + (2166623563875403/100000000000000 : ℝ)*(major2) + (1501647475908817/50000000000000 : ℝ)*(sp4) + (300319824348373/10000000000000 : ℝ)*(sp5) + (1501634132674893/50000000000000 : ℝ)*(sp6) + (270219298270071/20000000000000 : ℝ)*(sp7) + (96708333903/100000000000000 : ℝ)*(sp13) + (3335808481/12500000000000 : ℝ)*(sp14) + (43457169647/50000000000000 : ℝ)*(sp15) + (84448962855603/6250000000000 : ℝ)*(f.failure) + (1501647475908817/50000000000000 : ℝ)*(f.sum) + (9509801864871/2357000000000000000000000000 : ℝ)*base65 + (15618984240376828267/1178500000000000000000000000000000 : ℝ)*base68 + (7030869392089828267/1178500000000000000000000000000000 : ℝ)*base70 + (2057415468308828267/1178500000000000000000000000000000 : ℝ)*base72 + (775579481631/94280000000000000000000000 : ℝ)*base74 + (5978635110196671733/1178500000000000000000000000000000 : ℝ)*base75 + (1583682209301171733/1178500000000000000000000000000000 : ℝ)*base77 + (6968945109589828267/1178500000000000000000000000000000 : ℝ)*base80 + (9089313659543/2357000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (262073/78125000000000000000 : ℝ)*base90 + (262073/78125000000000000000 : ℝ)*base92 + (262073/78125000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (1169/2000 : ℝ) ≤ (172214798760147201499486535853729/294625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7620619/5000000000000 : ℝ)*(upper0) + (17023201/100000000000000 : ℝ)*(upper3) + (114744231/100000000000000 : ℝ)*(upper4) + (1120147759506729/50000000000000 : ℝ)*(major0) + (1120147759506729/50000000000000 : ℝ)*(major1) + (1120147759506729/50000000000000 : ℝ)*(major2) + (153198698433329/5000000000000 : ℝ)*(sp0) + (3063973745611/100000000000 : ℝ)*(sp1) + (153196590979913/5000000000000 : ℝ)*(sp2) + (1397126025943739/100000000000000 : ℝ)*(sp3) + (1342935653/25000000000000 : ℝ)*(sp5) + (5148687033/100000000000000 : ℝ)*(sp8) + (5912219419/12500000000000 : ℝ)*(sp10) + (913776307/50000000000000 : ℝ)*(sp11) + (698563926748177/50000000000000 : ℝ)*(f.failure) + (765994779338403/25000000000000 : ℝ)*(f.sum) + (385466184283/94280000000000000000000000 : ℝ)*base65 + (6053932585029682919/589250000000000000000000000000000 : ℝ)*base67 + (2845725466555932919/589250000000000000000000000000000 : ℝ)*base69 + (8175074956529932919/589250000000000000000000000000000 : ℝ)*base71 + (416502290527/18414062500000000000000000 : ℝ)*base73 + (6093733247061432919/589250000000000000000000000000000 : ℝ)*base75 + (6838913107586932919/589250000000000000000000000000000 : ℝ)*base77 + (20691329788333432919/589250000000000000000000000000000 : ℝ)*base79 + (299140964423/294625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (977343/625000000000000000000 : ℝ)*base89 + (977343/625000000000000000000 : ℝ)*base91 + (977343/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (799/1000 : ℝ) ≤ (7356679345192326155312973927177/9207031250000000000000000000000 : ℝ) := by norm_num
    linear_combination (4790509/10000000000000 : ℝ)*(upper0) + (27220463/50000000000000 : ℝ)*(lower3) + (65202137/100000000000000 : ℝ)*(upper4) + (152400873749083/6250000000000 : ℝ)*(major0) + (152400873749083/6250000000000 : ℝ)*(major1) + (152400873749083/6250000000000 : ℝ)*(major2) + (15303688779/20000000000000 : ℝ)*(sp1) + (2616977409/50000000000000 : ℝ)*(sp3) + (3301696131/100000000000000 : ℝ)*(sp4) + (832376795802903/25000000000000 : ℝ)*(sp8) + (208089724977117/6250000000000 : ℝ)*(sp9) + (3329512118077767/100000000000000 : ℝ)*(sp10) + (30413526566237/2000000000000 : ℝ)*(sp11) + (204146253/12500000000000 : ℝ)*(sp12) + (380170390566667/25000000000000 : ℝ)*(f.failure) + (3329512118077767/100000000000000 : ℝ)*(f.sum) + (17194415613821/2357000000000000000000000000 : ℝ)*base65 + (439827213113395213/73656250000000000000000000000000 : ℝ)*base67 + (707318663119301463/73656250000000000000000000000000 : ℝ)*base69 + (1241179548636113963/73656250000000000000000000000000 : ℝ)*base71 + (4097578308931/2357000000000000000000000000 : ℝ)*base73 + (669104421111395213/73656250000000000000000000000000 : ℝ)*base75 + (545369606109895213/73656250000000000000000000000000 : ℝ)*base77 + (377141332869613963/73656250000000000000000000000000 : ℝ)*base79 + (6884630360381/1178500000000000000000000000 : ℝ)*base81 + (3218747/312500000000000000000 : ℝ)*base90 + (3218747/312500000000000000000 : ℝ)*base92 + (3218747/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-42877/50000 : ℝ) ≤ (-3158069185515526998686603459703/3682812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (41747/1000000000000 : ℝ)*(lower0) + (54416077/100000000000000 : ℝ)*(lower1) + (13296089/50000000000000 : ℝ)*(lower2) + (451051/100000000000000 : ℝ)*(lower3) + (7102229/4000000000000 : ℝ)*(lower4) + (15478634920391/625000000000 : ℝ)*(major0) + (15478634920391/625000000000 : ℝ)*(major1) + (15478634920391/625000000000 : ℝ)*(major2) + (2432898707/2500000000000 : ℝ)*(sp6) + (18254211679/50000000000000 : ℝ)*(sp7) + (859315697560527/25000000000000 : ℝ)*(sp12) + (859315697560527/25000000000000 : ℝ)*(sp13) + (3437165474293827/100000000000000 : ℝ)*(sp14) + (772223864663877/50000000000000 : ℝ)*(sp15) + (193060529718889/12500000000000 : ℝ)*(f.failure) + (859315697560527/25000000000000 : ℝ)*(f.sum) + (2470410192849/1178500000000000000000000000 : ℝ)*base66 + (6263763759494901/7365625000000000000000000000000 : ℝ)*base67 + (3725371016436349/7365625000000000000000000000000 : ℝ)*base70 + (50467594209511349/7365625000000000000000000000000 : ℝ)*base72 + (1601247954867/294625000000000000000000000 : ℝ)*base73 + (10504935785776151/7365625000000000000000000000000 : ℝ)*base75 + (8648174591538569/1841406250000000000000000000000 : ℝ)*base77 + (47148011758244901/7365625000000000000000000000000 : ℝ)*base79 + (19540377908173/2357000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1136249/156250000000000000000 : ℝ)*base90 + (1136249/156250000000000000000 : ℝ)*base92 + (1136249/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1474_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20043759/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (269/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3981/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(1169/2000 : ℝ) else (799/1000 : ℝ) ≤ X j i ∧ X j i ≤ (42877/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1474_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1474_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20043759/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10759/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3981/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(1169/2000 : ℝ) else (799/1000 : ℝ) ≤ X j i ∧ X j i ≤ (42877/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1474_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1474_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4443/1024 : ℝ) ≤ p) (hpb : p ≤ (4445/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (20043759/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10759/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(3981/6250 : ℝ) ≤ X j i ∧ X j i ≤ -(1169/2000 : ℝ) else (799/1000 : ℝ) ≤ X j i ∧ X j i ≤ (42877/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1474_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
