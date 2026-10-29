-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1614_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:51:53.816097+00:00
-- url     : https://prove2.me/submissions/ee6aade5-a610-44e0-a4c0-7c417d986e42

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
theorem support_rectangle_w1614_s3_0 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1694162429/10000000000 : ℝ)*x 0 + (5458730343/10000000000 : ℝ)*x 1 + (2590373937/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1694162429/10000000000 : ℝ)^4775 ≤ (5217164206689/50000000000000 : ℝ)^3751 := by
    have hnat : (1694162429 : ℕ)^4775*50000000000000^3751 ≤ 5217164206689^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1694162429 10000000000 5217164206689 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5458730343/10000000000 : ℝ)^4775 ≤ (46272106526807/100000000000000 : ℝ)^3751 := by
    have hnat : (5458730343 : ℕ)^4775*100000000000000^3751 ≤ 46272106526807^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458730343 10000000000 46272106526807 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590373937/5000000000 : ℝ)^4775 ≤ (43293565041251/100000000000000 : ℝ)^3751 := by
    have hnat : (2590373937 : ℕ)^4775*100000000000000^3751 ≤ 43293565041251^3751*5000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590373937 5000000000 43293565041251 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1694162429/10000000000 : ℝ), (5458730343/10000000000 : ℝ), (2590373937/5000000000 : ℝ)] ![(5217164206689/50000000000000 : ℝ), (46272106526807/100000000000000 : ℝ), (43293565041251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1694162429/10000000000 : ℝ)|^4775 ≤ (5217164206689/50000000000000 : ℝ)^3751
        have hw : |(-1694162429/10000000000 : ℝ)|=(1694162429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5458730343/10000000000 : ℝ)|^4775 ≤ (46272106526807/100000000000000 : ℝ)^3751
        have hw : |(5458730343/10000000000 : ℝ)|=(5458730343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590373937/5000000000 : ℝ)|^4775 ≤ (43293565041251/100000000000000 : ℝ)^3751
        have hw : |(2590373937/5000000000 : ℝ)|=(2590373937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s3_1 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676565493/5000000000 : ℝ)*x 0 + (-73499709/400000000 : ℝ)*x 1 + (1036149543/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676565493/5000000000 : ℝ)^4775 ≤ (22567813663287/50000000000000 : ℝ)^3751 := by
    have hnat : (2676565493 : ℕ)^4775*50000000000000^3751 ≤ 22567813663287^3751*5000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676565493 5000000000 22567813663287 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (73499709/400000000 : ℝ)^4775 ≤ (5785404655229/50000000000000 : ℝ)^3751 := by
    have hnat : (73499709 : ℕ)^4775*50000000000000^3751 ≤ 5785404655229^3751*400000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73499709 400000000 5785404655229 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036149543/2000000000 : ℝ)^4775 ≤ (2164678167491/5000000000000 : ℝ)^3751 := by
    have hnat : (1036149543 : ℕ)^4775*5000000000000^3751 ≤ 2164678167491^3751*2000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036149543 2000000000 2164678167491 5000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676565493/5000000000 : ℝ), (-73499709/400000000 : ℝ), (1036149543/2000000000 : ℝ)] ![(22567813663287/50000000000000 : ℝ), (5785404655229/50000000000000 : ℝ), (2164678167491/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676565493/5000000000 : ℝ)|^4775 ≤ (22567813663287/50000000000000 : ℝ)^3751
        have hw : |(2676565493/5000000000 : ℝ)|=(2676565493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-73499709/400000000 : ℝ)|^4775 ≤ (5785404655229/50000000000000 : ℝ)^3751
        have hw : |(-73499709/400000000 : ℝ)|=(73499709/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1036149543/2000000000 : ℝ)|^4775 ≤ (2164678167491/5000000000000 : ℝ)^3751
        have hw : |(1036149543/2000000000 : ℝ)|=(1036149543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s3_2 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338282803/2500000000 : ℝ)*x 0 + (1036149541/2000000000 : ℝ)*x 1 + (-367498487/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338282803/2500000000 : ℝ)^4775 ≤ (22567814876163/50000000000000 : ℝ)^3751 := by
    have hnat : (1338282803 : ℕ)^4775*50000000000000^3751 ≤ 22567814876163^3751*2500000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338282803 2500000000 22567814876163 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036149541/2000000000 : ℝ)^4775 ≤ (43293563243441/100000000000000 : ℝ)^3751 := by
    have hnat : (1036149541 : ℕ)^4775*100000000000000^3751 ≤ 43293563243441^3751*2000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036149541 2000000000 43293563243441 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (367498487/2000000000 : ℝ)^4775 ≤ (5785403492891/50000000000000 : ℝ)^3751 := by
    have hnat : (367498487 : ℕ)^4775*50000000000000^3751 ≤ 5785403492891^3751*2000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      367498487 2000000000 5785403492891 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338282803/2500000000 : ℝ), (1036149541/2000000000 : ℝ), (-367498487/2000000000 : ℝ)] ![(22567814876163/50000000000000 : ℝ), (43293563243441/100000000000000 : ℝ), (5785403492891/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338282803/2500000000 : ℝ)|^4775 ≤ (22567814876163/50000000000000 : ℝ)^3751
        have hw : |(1338282803/2500000000 : ℝ)|=(1338282803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036149541/2000000000 : ℝ)|^4775 ≤ (43293563243441/100000000000000 : ℝ)^3751
        have hw : |(1036149541/2000000000 : ℝ)|=(1036149541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-367498487/2000000000 : ℝ)|^4775 ≤ (5785403492891/50000000000000 : ℝ)^3751
        have hw : |(-367498487/2000000000 : ℝ)|=(367498487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s3_3 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (526149097/1250000000 : ℝ)*x 0 + (969140563/2500000000 : ℝ)*x 1 + (4563259859/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526149097/1250000000 : ℝ)^4775 ≤ (33235896475483/100000000000000 : ℝ)^3751 := by
    have hnat : (526149097 : ℕ)^4775*100000000000000^3751 ≤ 33235896475483^3751*1250000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526149097 1250000000 33235896475483 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (969140563/2500000000 : ℝ)^4775 ≤ (7482302477061/25000000000000 : ℝ)^3751 := by
    have hnat : (969140563 : ℕ)^4775*25000000000000^3751 ≤ 7482302477061^3751*2500000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969140563 2500000000 7482302477061 25000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4563259859/10000000000 : ℝ)^4775 ≤ (18417446804269/50000000000000 : ℝ)^3751 := by
    have hnat : (4563259859 : ℕ)^4775*50000000000000^3751 ≤ 18417446804269^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4563259859 10000000000 18417446804269 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(526149097/1250000000 : ℝ), (969140563/2500000000 : ℝ), (4563259859/10000000000 : ℝ)] ![(33235896475483/100000000000000 : ℝ), (7482302477061/25000000000000 : ℝ), (18417446804269/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(526149097/1250000000 : ℝ)|^4775 ≤ (33235896475483/100000000000000 : ℝ)^3751
        have hw : |(526149097/1250000000 : ℝ)|=(526149097/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(969140563/2500000000 : ℝ)|^4775 ≤ (7482302477061/25000000000000 : ℝ)^3751
        have hw : |(969140563/2500000000 : ℝ)|=(969140563/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4563259859/10000000000 : ℝ)|^4775 ≤ (18417446804269/50000000000000 : ℝ)^3751
        have hw : |(4563259859/10000000000 : ℝ)|=(4563259859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s3_4 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-847116377/5000000000 : ℝ)*x 0 + (5182824193/10000000000 : ℝ)*x 1 + (2728316061/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (847116377/5000000000 : ℝ)^4775 ≤ (5217439894759/50000000000000 : ℝ)^3751 := by
    have hnat : (847116377 : ℕ)^4775*50000000000000^3751 ≤ 5217439894759^3751*5000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847116377 5000000000 5217439894759 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182824193/10000000000 : ℝ)^4775 ≤ (8663130797893/20000000000000 : ℝ)^3751 := by
    have hnat : (5182824193 : ℕ)^4775*20000000000000^3751 ≤ 8663130797893^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182824193 10000000000 8663130797893 20000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2728316061/5000000000 : ℝ)^4775 ≤ (23124733108053/50000000000000 : ℝ)^3751 := by
    have hnat : (2728316061 : ℕ)^4775*50000000000000^3751 ≤ 23124733108053^3751*5000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728316061 5000000000 23124733108053 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-847116377/5000000000 : ℝ), (5182824193/10000000000 : ℝ), (2728316061/5000000000 : ℝ)] ![(5217439894759/50000000000000 : ℝ), (8663130797893/20000000000000 : ℝ), (23124733108053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-847116377/5000000000 : ℝ)|^4775 ≤ (5217439894759/50000000000000 : ℝ)^3751
        have hw : |(-847116377/5000000000 : ℝ)|=(847116377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182824193/10000000000 : ℝ)|^4775 ≤ (8663130797893/20000000000000 : ℝ)^3751
        have hw : |(5182824193/10000000000 : ℝ)|=(5182824193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2728316061/5000000000 : ℝ)|^4775 ≤ (23124733108053/50000000000000 : ℝ)^3751
        have hw : |(2728316061/5000000000 : ℝ)|=(2728316061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s3_5 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319813211/2500000000 : ℝ)*x 0 + (-1561608113/10000000000 : ℝ)*x 1 + (2728316057/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319813211/2500000000 : ℝ)^4775 ≤ (22172080681621/50000000000000 : ℝ)^3751 := by
    have hnat : (1319813211 : ℕ)^4775*50000000000000^3751 ≤ 22172080681621^3751*2500000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319813211 2500000000 22172080681621 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1561608113/10000000000 : ℝ)^4775 ≤ (9406372492961/100000000000000 : ℝ)^3751 := by
    have hnat : (1561608113 : ℕ)^4775*100000000000000^3751 ≤ 9406372492961^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1561608113 10000000000 9406372492961 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2728316057/5000000000 : ℝ)^4775 ≤ (11562366532447/25000000000000 : ℝ)^3751 := by
    have hnat : (2728316057 : ℕ)^4775*25000000000000^3751 ≤ 11562366532447^3751*5000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728316057 5000000000 11562366532447 25000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319813211/2500000000 : ℝ), (-1561608113/10000000000 : ℝ), (2728316057/5000000000 : ℝ)] ![(22172080681621/50000000000000 : ℝ), (9406372492961/100000000000000 : ℝ), (11562366532447/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319813211/2500000000 : ℝ)|^4775 ≤ (22172080681621/50000000000000 : ℝ)^3751
        have hw : |(1319813211/2500000000 : ℝ)|=(1319813211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1561608113/10000000000 : ℝ)|^4775 ≤ (9406372492961/100000000000000 : ℝ)^3751
        have hw : |(-1561608113/10000000000 : ℝ)|=(1561608113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2728316057/5000000000 : ℝ)|^4775 ≤ (11562366532447/25000000000000 : ℝ)^3751
        have hw : |(2728316057/5000000000 : ℝ)|=(2728316057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s3_6 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055850567/2000000000 : ℝ)*x 0 + (5456632107/10000000000 : ℝ)*x 1 + (-312321627/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055850567/2000000000 : ℝ)^4775 ≤ (44344161267007/100000000000000 : ℝ)^3751 := by
    have hnat : (1055850567 : ℕ)^4775*100000000000000^3751 ≤ 44344161267007^3751*2000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055850567 2000000000 44344161267007 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5456632107/10000000000 : ℝ)^4775 ≤ (46249466054261/100000000000000 : ℝ)^3751 := by
    have hnat : (5456632107 : ℕ)^4775*100000000000000^3751 ≤ 46249466054261^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456632107 10000000000 46249466054261 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (312321627/2000000000 : ℝ)^4775 ≤ (1881274532331/20000000000000 : ℝ)^3751 := by
    have hnat : (312321627 : ℕ)^4775*20000000000000^3751 ≤ 1881274532331^3751*2000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312321627 2000000000 1881274532331 20000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055850567/2000000000 : ℝ), (5456632107/10000000000 : ℝ), (-312321627/2000000000 : ℝ)] ![(44344161267007/100000000000000 : ℝ), (46249466054261/100000000000000 : ℝ), (1881274532331/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055850567/2000000000 : ℝ)|^4775 ≤ (44344161267007/100000000000000 : ℝ)^3751
        have hw : |(1055850567/2000000000 : ℝ)|=(1055850567/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5456632107/10000000000 : ℝ)|^4775 ≤ (46249466054261/100000000000000 : ℝ)^3751
        have hw : |(5456632107/10000000000 : ℝ)|=(5456632107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-312321627/2000000000 : ℝ)|^4775 ≤ (1881274532331/20000000000000 : ℝ)^3751
        have hw : |(-312321627/2000000000 : ℝ)|=(312321627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s3_7 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4209366877/10000000000 : ℝ)*x 0 + (4558130167/10000000000 : ℝ)*x 1 + (194087283/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4209366877/10000000000 : ℝ)^4775 ≤ (16618823238873/50000000000000 : ℝ)^3751 := by
    have hnat : (4209366877 : ℕ)^4775*50000000000000^3751 ≤ 16618823238873^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4209366877 10000000000 16618823238873 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4558130167/10000000000 : ℝ)^4775 ≤ (4597773828769/12500000000000 : ℝ)^3751 := by
    have hnat : (4558130167 : ℕ)^4775*12500000000000^3751 ≤ 4597773828769^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4558130167 10000000000 4597773828769 12500000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (194087283/500000000 : ℝ)^4775 ≤ (2998016286927/10000000000000 : ℝ)^3751 := by
    have hnat : (194087283 : ℕ)^4775*10000000000000^3751 ≤ 2998016286927^3751*500000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194087283 500000000 2998016286927 10000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4209366877/10000000000 : ℝ), (4558130167/10000000000 : ℝ), (194087283/500000000 : ℝ)] ![(16618823238873/50000000000000 : ℝ), (4597773828769/12500000000000 : ℝ), (2998016286927/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4209366877/10000000000 : ℝ)|^4775 ≤ (16618823238873/50000000000000 : ℝ)^3751
        have hw : |(4209366877/10000000000 : ℝ)|=(4209366877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4558130167/10000000000 : ℝ)|^4775 ≤ (4597773828769/12500000000000 : ℝ)^3751
        have hw : |(4558130167/10000000000 : ℝ)|=(4558130167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(194087283/500000000 : ℝ)|^4775 ≤ (2998016286927/10000000000000 : ℝ)^3751
        have hw : |(194087283/500000000 : ℝ)|=(194087283/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1614_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43378611/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16477/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10333/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10451/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8173/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16477/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10333/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16477/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10333/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16477/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10333/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16477/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10333/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16477/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10333/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16477/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10333/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10333/100000 : ℝ) ^ (4771/1024 : ℝ) ≤ (159581969504591/6250000000000000000 : ℝ) := by
    have hpowers : (10333/100000 : ℝ)^4771 ≤ (159581969504591/6250000000000000000 : ℝ)^1024 := by
      have hnat : (10333 : ℕ)^4771*6250000000000000000^1024 ≤ 159581969504591^1024*100000^4771 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10333 100000 159581969504591 6250000000000000000 4771 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10333/100000 : ℝ)) (X := (159581969504591/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16477/100000 : ℝ) ^ (4771/1024 : ℝ) ≤ (350844417827977/1562500000000000000 : ℝ) := by
    have hpowers : (16477/100000 : ℝ)^4771 ≤ (350844417827977/1562500000000000000 : ℝ)^1024 := by
      have hnat : (16477 : ℕ)^4771*1562500000000000000^1024 ≤ 350844417827977^1024*100000^4771 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16477 100000 350844417827977 1562500000000000000 4771 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16477/100000 : ℝ)) (X := (350844417827977/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125159581969504591/3125000000000000000 : ℝ) ≤ (5000054800640531/5000000000000000 : ℝ) ^ (4771/1024 : ℝ) := by
    have hpowers : (3125159581969504591/3125000000000000000 : ℝ)^1024 ≤ (5000054800640531/5000000000000000 : ℝ)^4771 := by
      have hnat : (3125159581969504591 : ℕ)^1024*5000000000000000^4771 ≤ 5000054800640531^4771*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125159581969504591 3125000000000000000 5000054800640531 5000000000000000 1024 4771 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000054800640531/5000000000000000 : ℝ)) (X := (3125159581969504591/3125000000000000000 : ℝ)) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6251562959640816499/6250000000000000000 : ℝ) ≤ (10000536680286453/10000000000000000 : ℝ) ^ (4771/1024 : ℝ) := by
    have hpowers : (6251562959640816499/6250000000000000000 : ℝ)^1024 ≤ (10000536680286453/10000000000000000 : ℝ)^4771 := by
      have hnat : (6251562959640816499 : ℕ)^1024*10000000000000000^4771 ≤ 10000536680286453^4771*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251562959640816499 6250000000000000000 10000536680286453 10000000000000000 1024 4771 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000536680286453/10000000000000000 : ℝ)) (X := (6251562959640816499/6250000000000000000 : ℝ)) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (781600844417827977/781250000000000000 : ℝ) ≤ (2500240939822961/2500000000000000 : ℝ) ^ (4771/1024 : ℝ) := by
    have hpowers : (781600844417827977/781250000000000000 : ℝ)^1024 ≤ (2500240939822961/2500000000000000 : ℝ)^4771 := by
      have hnat : (781600844417827977 : ℕ)^1024*2500000000000000^4771 ≤ 2500240939822961^4771*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781600844417827977 781250000000000000 2500240939822961 2500000000000000 1024 4771 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500240939822961/2500000000000000 : ℝ)) (X := (781600844417827977/781250000000000000 : ℝ)) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(159581969504591/6250000000000000000 : ℝ) ≤ ((30715923687772717261/30720000000000000000 : ℝ)+2*(427079005391/614400000000000 : ℝ)*(10333/100000 : ℝ))^(4771/1024 : ℝ) := by
    rw [show (30715923687772717261/30720000000000000000 : ℝ)+2*(427079005391/614400000000000 : ℝ)*(10333/100000 : ℝ)=(5000054800640531/5000000000000000 : ℝ) by norm_num, show 1+2*(159581969504591/6250000000000000000 : ℝ)=(3125159581969504591/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(350844417827977/1562500000000000000 : ℝ)+(159581969504591/6250000000000000000 : ℝ) ≤ ((30715923687772717261/30720000000000000000 : ℝ)+(427079005391/614400000000000 : ℝ)*((16477/100000 : ℝ)+(10333/100000 : ℝ)))^(4771/1024 : ℝ) := by
    rw [show (30715923687772717261/30720000000000000000 : ℝ)+(427079005391/614400000000000 : ℝ)*((16477/100000 : ℝ)+(10333/100000 : ℝ))=(10000536680286453/10000000000000000 : ℝ) by norm_num, show 1+(350844417827977/1562500000000000000 : ℝ)+(159581969504591/6250000000000000000 : ℝ)=(6251562959640816499/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(350844417827977/1562500000000000000 : ℝ) ≤ ((30715923687772717261/30720000000000000000 : ℝ)+2*(427079005391/614400000000000 : ℝ)*(16477/100000 : ℝ))^(4771/1024 : ℝ) := by
    rw [show (30715923687772717261/30720000000000000000 : ℝ)+2*(427079005391/614400000000000 : ℝ)*(16477/100000 : ℝ)=(2500240939822961/2500000000000000 : ℝ) by norm_num, show 1+2*(350844417827977/1562500000000000000 : ℝ)=(781600844417827977/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (30715923687772717261/30720000000000000000 : ℝ)*(X 1 0+X 2 0)+(427079005391/614400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4771/1024 : ℝ)) (lo := (10333/100000 : ℝ)) (hi := (16477/100000 : ℝ)) (c := (30715923687772717261/30720000000000000000 : ℝ)) (alpha := (427079005391/614400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (30715923687772717261/30720000000000000000 : ℝ)*(X 0 1+X 2 1)+(427079005391/614400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4771/1024 : ℝ)) (lo := (10333/100000 : ℝ)) (hi := (16477/100000 : ℝ)) (c := (30715923687772717261/30720000000000000000 : ℝ)) (alpha := (427079005391/614400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (30715923687772717261/30720000000000000000 : ℝ)*(X 0 2+X 1 2)+(427079005391/614400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4771/1024 : ℝ)) (lo := (10333/100000 : ℝ)) (hi := (16477/100000 : ℝ)) (c := (30715923687772717261/30720000000000000000 : ℝ)) (alpha := (427079005391/614400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1694162429/10000000000 : ℝ)*X 0 0+(5458730343/10000000000 : ℝ)*X 0 1+(2590373937/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676565493/5000000000 : ℝ)*X 1 0+(-73499709/400000000 : ℝ)*X 1 1+(1036149543/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338282803/2500000000 : ℝ)*X 2 0+(1036149541/2000000000 : ℝ)*X 2 1+(-367498487/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((526149097/1250000000 : ℝ)*X 0 0+(969140563/2500000000 : ℝ)*X 0 1+(4563259859/10000000000 : ℝ)*X 0 2+(526149097/1250000000 : ℝ)*X 1 0+(969140563/2500000000 : ℝ)*X 1 1+(4563259859/10000000000 : ℝ)*X 1 2+(526149097/1250000000 : ℝ)*X 2 0+(969140563/2500000000 : ℝ)*X 2 1+(4563259859/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-847116377/5000000000 : ℝ)*X 0 0+(5182824193/10000000000 : ℝ)*X 0 1+(2728316061/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1319813211/2500000000 : ℝ)*X 1 0+(-1561608113/10000000000 : ℝ)*X 1 1+(2728316057/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1055850567/2000000000 : ℝ)*X 2 0+(5456632107/10000000000 : ℝ)*X 2 1+(-312321627/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4209366877/10000000000 : ℝ)*X 0 0+(4558130167/10000000000 : ℝ)*X 0 1+(194087283/500000000 : ℝ)*X 0 2+(4209366877/10000000000 : ℝ)*X 1 0+(4558130167/10000000000 : ℝ)*X 1 1+(194087283/500000000 : ℝ)*X 1 2+(4209366877/10000000000 : ℝ)*X 2 0+(4558130167/10000000000 : ℝ)*X 2 1+(194087283/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (740953056523657221297638049/128000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (668501129/100000000000000 : ℝ)*(base19) + (792359057/100000000000000 : ℝ)*(base23) + (9261059/50000000000000 : ℝ)*(upper4) + (95724543/50000000000000 : ℝ)*(upper5) + (1263404094774291/50000000000000 : ℝ)*(major0) + (1263404094774291/50000000000000 : ℝ)*(major1) + (1263404094774291/50000000000000 : ℝ)*(major2) + (3597353742478491/100000000000000 : ℝ)*(sp0) + (1798681339174441/50000000000000 : ℝ)*(sp1) + (1798681515779149/50000000000000 : ℝ)*(sp2) + (728124626897221/50000000000000 : ℝ)*(sp3) + (630089929/6250000000000 : ℝ)*(sp4) + (477067343/100000000000000 : ℝ)*(sp5) + (97138401/3125000000000 : ℝ)*(sp7) + (58250094488931/4000000000000 : ℝ)*(f.failure) + (1798681911958677/50000000000000 : ℝ)*(f.sum) + (24879125688607/5120000000000000000000000000 : ℝ)*base65 + (2784387760815262317/512000000000000000000000000000000 : ℝ)*base67 + (3466385663151262317/512000000000000000000000000000000 : ℝ)*base69 + (5098467859631262317/512000000000000000000000000000000 : ℝ)*base71 + (1247465871647/5120000000000000000000000000 : ℝ)*base73 + (4629552285871262317/512000000000000000000000000000000 : ℝ)*base75 + (1434357251247262317/512000000000000000000000000000000 : ℝ)*base77 + (4128132904784737683/512000000000000000000000000000000 : ℝ)*base80 + (21517770900767/5120000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (345159/100000000000000000000 : ℝ)*base90 + (345159/100000000000000000000 : ℝ)*base92 + (345159/100000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (528657532526950049898836893/64000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1246948239/100000000000000 : ℝ)*(base19) + (1343051967/100000000000000 : ℝ)*(base23) + (167032901/100000000000000 : ℝ)*(upper3) + (50549469/100000000000000 : ℝ)*(lower4) + (187291099/100000000000000 : ℝ)*(upper5) + (641330473462487/25000000000000 : ℝ)*(major0) + (641330473462487/25000000000000 : ℝ)*(major1) + (641330473462487/25000000000000 : ℝ)*(major2) + (14374854211/100000000000000 : ℝ)*(sp1) + (14844917973/100000000000000 : ℝ)*(sp2) + (228262181095393/6250000000000 : ℝ)*(sp4) + (1826089637861919/50000000000000 : ℝ)*(sp5) + (913044677389087/25000000000000 : ℝ)*(sp6) + (46201519213473/3125000000000 : ℝ)*(sp7) + (46201519213473/3125000000000 : ℝ)*(f.failure) + (228262181095393/6250000000000 : ℝ)*(f.sum) + (5618282745817/7680000000000000000000000000 : ℝ)*base65 + (3669651851183738107/768000000000000000000000000000000 : ℝ)*base67 + (1517848254383738107/768000000000000000000000000000000 : ℝ)*base69 + (2435022166608261893/768000000000000000000000000000000 : ℝ)*base72 + (40370114377177/7680000000000000000000000000 : ℝ)*base73 + (993850869935738107/768000000000000000000000000000000 : ℝ)*base75 + (1742481164207738107/768000000000000000000000000000000 : ℝ)*base77 + (7927765169327738107/768000000000000000000000000000000 : ℝ)*base79 + (672400684583/7680000000000000000000000000 : ℝ)*base82 + (648997/78125000000000000000 : ℝ)*base90 + (648997/78125000000000000000 : ℝ)*base92 + (648997/78125000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1614_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43378611/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16477/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10333/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10451/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8173/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1614_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1614_s4_0 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-847134033/5000000000 : ℝ)*x 0 + (5458199257/10000000000 : ℝ)*x 1 + (2590604361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (847134033/5000000000 : ℝ)^4775 ≤ (2608789163021/25000000000000 : ℝ)^3751 := by
    have hnat : (847134033 : ℕ)^4775*25000000000000^3751 ≤ 2608789163021^3751*5000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      847134033 5000000000 2608789163021 25000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5458199257/10000000000 : ℝ)^4775 ≤ (9253275151233/20000000000000 : ℝ)^3751 := by
    have hnat : (5458199257 : ℕ)^4775*20000000000000^3751 ≤ 9253275151233^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458199257 10000000000 9253275151233 20000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590604361/5000000000 : ℝ)^4775 ≤ (21649233785197/50000000000000 : ℝ)^3751 := by
    have hnat : (2590604361 : ℕ)^4775*50000000000000^3751 ≤ 21649233785197^3751*5000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590604361 5000000000 21649233785197 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-847134033/5000000000 : ℝ), (5458199257/10000000000 : ℝ), (2590604361/5000000000 : ℝ)] ![(2608789163021/25000000000000 : ℝ), (9253275151233/20000000000000 : ℝ), (21649233785197/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-847134033/5000000000 : ℝ)|^4775 ≤ (2608789163021/25000000000000 : ℝ)^3751
        have hw : |(-847134033/5000000000 : ℝ)|=(847134033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5458199257/10000000000 : ℝ)|^4775 ≤ (9253275151233/20000000000000 : ℝ)^3751
        have hw : |(5458199257/10000000000 : ℝ)|=(5458199257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590604361/5000000000 : ℝ)|^4775 ≤ (21649233785197/50000000000000 : ℝ)^3751
        have hw : |(2590604361/5000000000 : ℝ)|=(2590604361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s4_1 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352988953/10000000000 : ℝ)*x 0 + (-918535549/5000000000 : ℝ)*x 1 + (5181208721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352988953/10000000000 : ℝ)^4775 ≤ (45134102832951/100000000000000 : ℝ)^3751 := by
    have hnat : (5352988953 : ℕ)^4775*100000000000000^3751 ≤ 45134102832951^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352988953 10000000000 45134102832951 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (918535549/5000000000 : ℝ)^4775 ≤ (11567429602059/100000000000000 : ℝ)^3751 := by
    have hnat : (918535549 : ℕ)^4775*100000000000000^3751 ≤ 11567429602059^3751*5000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      918535549 5000000000 11567429602059 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5181208721/10000000000 : ℝ)^4775 ≤ (10824616889939/25000000000000 : ℝ)^3751 := by
    have hnat : (5181208721 : ℕ)^4775*25000000000000^3751 ≤ 10824616889939^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181208721 10000000000 10824616889939 25000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352988953/10000000000 : ℝ), (-918535549/5000000000 : ℝ), (5181208721/10000000000 : ℝ)] ![(45134102832951/100000000000000 : ℝ), (11567429602059/100000000000000 : ℝ), (10824616889939/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352988953/10000000000 : ℝ)|^4775 ≤ (45134102832951/100000000000000 : ℝ)^3751
        have hw : |(5352988953/10000000000 : ℝ)|=(5352988953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-918535549/5000000000 : ℝ)|^4775 ≤ (11567429602059/100000000000000 : ℝ)^3751
        have hw : |(-918535549/5000000000 : ℝ)|=(918535549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5181208721/10000000000 : ℝ)|^4775 ≤ (10824616889939/25000000000000 : ℝ)^3751
        have hw : |(5181208721/10000000000 : ℝ)|=(5181208721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s4_2 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338247237/2500000000 : ℝ)*x 0 + (5181208719/10000000000 : ℝ)*x 1 + (-367414221/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338247237/2500000000 : ℝ)^4775 ≤ (9026820555857/20000000000000 : ℝ)^3751 := by
    have hnat : (1338247237 : ℕ)^4775*20000000000000^3751 ≤ 9026820555857^3751*2500000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338247237 2500000000 9026820555857 20000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181208719/10000000000 : ℝ)^4775 ≤ (541230844231/1250000000000 : ℝ)^3751 := by
    have hnat : (5181208719 : ℕ)^4775*1250000000000^3751 ≤ 541230844231^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181208719 10000000000 541230844231 1250000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (367414221/2000000000 : ℝ)^4775 ≤ (11567429658169/100000000000000 : ℝ)^3751 := by
    have hnat : (367414221 : ℕ)^4775*100000000000000^3751 ≤ 11567429658169^3751*2000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      367414221 2000000000 11567429658169 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338247237/2500000000 : ℝ), (5181208719/10000000000 : ℝ), (-367414221/2000000000 : ℝ)] ![(9026820555857/20000000000000 : ℝ), (541230844231/1250000000000 : ℝ), (11567429658169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338247237/2500000000 : ℝ)|^4775 ≤ (9026820555857/20000000000000 : ℝ)^3751
        have hw : |(1338247237/2500000000 : ℝ)|=(1338247237/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181208719/10000000000 : ℝ)|^4775 ≤ (541230844231/1250000000000 : ℝ)^3751
        have hw : |(5181208719/10000000000 : ℝ)|=(5181208719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-367414221/2000000000 : ℝ)|^4775 ≤ (11567429658169/100000000000000 : ℝ)^3751
        have hw : |(-367414221/2000000000 : ℝ)|=(367414221/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s4_3 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4209262139/10000000000 : ℝ)*x 0 + (3877780283/10000000000 : ℝ)*x 1 + (2281013461/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4209262139/10000000000 : ℝ)^4775 ≤ (8309148421423/25000000000000 : ℝ)^3751 := by
    have hnat : (4209262139 : ℕ)^4775*25000000000000^3751 ≤ 8309148421423^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4209262139 10000000000 8309148421423 25000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3877780283/10000000000 : ℝ)^4775 ≤ (29941181496381/100000000000000 : ℝ)^3751 := by
    have hnat : (3877780283 : ℕ)^4775*100000000000000^3751 ≤ 29941181496381^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3877780283 10000000000 29941181496381 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2281013461/5000000000 : ℝ)^4775 ≤ (7364444962183/20000000000000 : ℝ)^3751 := by
    have hnat : (2281013461 : ℕ)^4775*20000000000000^3751 ≤ 7364444962183^3751*5000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2281013461 5000000000 7364444962183 20000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4209262139/10000000000 : ℝ), (3877780283/10000000000 : ℝ), (2281013461/5000000000 : ℝ)] ![(8309148421423/25000000000000 : ℝ), (29941181496381/100000000000000 : ℝ), (7364444962183/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4209262139/10000000000 : ℝ)|^4775 ≤ (8309148421423/25000000000000 : ℝ)^3751
        have hw : |(4209262139/10000000000 : ℝ)|=(4209262139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3877780283/10000000000 : ℝ)|^4775 ≤ (29941181496381/100000000000000 : ℝ)^3751
        have hw : |(3877780283/10000000000 : ℝ)|=(3877780283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2281013461/5000000000 : ℝ)|^4775 ≤ (7364444962183/20000000000000 : ℝ)^3751
        have hw : |(2281013461/5000000000 : ℝ)|=(2281013461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s4_4 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-423584407/2500000000 : ℝ)*x 0 + (2591635239/5000000000 : ℝ)*x 1 + (1364028961/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (423584407/2500000000 : ℝ)^4775 ≤ (10435702055249/100000000000000 : ℝ)^3751 := by
    have hnat : (423584407 : ℕ)^4775*100000000000000^3751 ≤ 10435702055249^3751*2500000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423584407 2500000000 10435702055249 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591635239/5000000000 : ℝ)^4775 ≤ (43320402114039/100000000000000 : ℝ)^3751 := by
    have hnat : (2591635239 : ℕ)^4775*100000000000000^3751 ≤ 43320402114039^3751*5000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591635239 5000000000 43320402114039 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1364028961/2500000000 : ℝ)^4775 ≤ (9248779163249/20000000000000 : ℝ)^3751 := by
    have hnat : (1364028961 : ℕ)^4775*20000000000000^3751 ≤ 9248779163249^3751*2500000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364028961 2500000000 9248779163249 20000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-423584407/2500000000 : ℝ), (2591635239/5000000000 : ℝ), (1364028961/2500000000 : ℝ)] ![(10435702055249/100000000000000 : ℝ), (43320402114039/100000000000000 : ℝ), (9248779163249/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-423584407/2500000000 : ℝ)|^4775 ≤ (10435702055249/100000000000000 : ℝ)^3751
        have hw : |(-423584407/2500000000 : ℝ)|=(423584407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591635239/5000000000 : ℝ)|^4775 ≤ (43320402114039/100000000000000 : ℝ)^3751
        have hw : |(2591635239/5000000000 : ℝ)|=(2591635239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1364028961/2500000000 : ℝ)|^4775 ≤ (9248779163249/20000000000000 : ℝ)^3751
        have hw : |(1364028961/2500000000 : ℝ)|=(1364028961/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s4_5 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055875009/2000000000 : ℝ)*x 0 + (-781082023/5000000000 : ℝ)*x 1 + (54561159/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055875009/2000000000 : ℝ)^4775 ≤ (44345468034767/100000000000000 : ℝ)^3751 := by
    have hnat : (1055875009 : ℕ)^4775*100000000000000^3751 ≤ 44345468034767^3751*2000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055875009 2000000000 44345468034767 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (781082023/5000000000 : ℝ)^4775 ≤ (1176329442327/12500000000000 : ℝ)^3751 := by
    have hnat : (781082023 : ℕ)^4775*12500000000000^3751 ≤ 1176329442327^3751*5000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      781082023 5000000000 1176329442327 12500000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54561159/100000000 : ℝ)^4775 ≤ (11560974105113/25000000000000 : ℝ)^3751 := by
    have hnat : (54561159 : ℕ)^4775*25000000000000^3751 ≤ 11560974105113^3751*100000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54561159 100000000 11560974105113 25000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055875009/2000000000 : ℝ), (-781082023/5000000000 : ℝ), (54561159/100000000 : ℝ)] ![(44345468034767/100000000000000 : ℝ), (1176329442327/12500000000000 : ℝ), (11560974105113/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055875009/2000000000 : ℝ)|^4775 ≤ (44345468034767/100000000000000 : ℝ)^3751
        have hw : |(1055875009/2000000000 : ℝ)|=(1055875009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-781082023/5000000000 : ℝ)|^4775 ≤ (1176329442327/12500000000000 : ℝ)^3751
        have hw : |(-781082023/5000000000 : ℝ)|=(781082023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54561159/100000000 : ℝ)|^4775 ≤ (11560974105113/25000000000000 : ℝ)^3751
        have hw : |(54561159/100000000 : ℝ)|=(54561159/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s4_6 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639687567/5000000000 : ℝ)*x 0 + (1091223177/2000000000 : ℝ)*x 1 + (-781081971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639687567/5000000000 : ℝ)^4775 ≤ (4434546898643/10000000000000 : ℝ)^3751 := by
    have hnat : (2639687567 : ℕ)^4775*10000000000000^3751 ≤ 4434546898643^3751*5000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639687567 5000000000 4434546898643 10000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091223177/2000000000 : ℝ)^4775 ≤ (46243896258611/100000000000000 : ℝ)^3751 := by
    have hnat : (1091223177 : ℕ)^4775*100000000000000^3751 ≤ 46243896258611^3751*2000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091223177 2000000000 46243896258611 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (781081971/5000000000 : ℝ)^4775 ≤ (9410634741077/100000000000000 : ℝ)^3751 := by
    have hnat : (781081971 : ℕ)^4775*100000000000000^3751 ≤ 9410634741077^3751*5000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      781081971 5000000000 9410634741077 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639687567/5000000000 : ℝ), (1091223177/2000000000 : ℝ), (-781081971/5000000000 : ℝ)] ![(4434546898643/10000000000000 : ℝ), (46243896258611/100000000000000 : ℝ), (9410634741077/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639687567/5000000000 : ℝ)|^4775 ≤ (4434546898643/10000000000000 : ℝ)^3751
        have hw : |(2639687567/5000000000 : ℝ)|=(2639687567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1091223177/2000000000 : ℝ)|^4775 ≤ (46243896258611/100000000000000 : ℝ)^3751
        have hw : |(1091223177/2000000000 : ℝ)|=(1091223177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-781081971/5000000000 : ℝ)|^4775 ≤ (9410634741077/100000000000000 : ℝ)^3751
        have hw : |(-781081971/5000000000 : ℝ)|=(781081971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s4_7 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4209434019/10000000000 : ℝ)*x 0 + (227846687/500000000 : ℝ)*x 1 + (3882926981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4209434019/10000000000 : ℝ)^4775 ≤ (3323832137089/10000000000000 : ℝ)^3751 := by
    have hnat : (4209434019 : ℕ)^4775*10000000000000^3751 ≤ 3323832137089^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4209434019 10000000000 3323832137089 10000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (227846687/500000000 : ℝ)^4775 ≤ (18384950372513/50000000000000 : ℝ)^3751 := by
    have hnat : (227846687 : ℕ)^4775*50000000000000^3751 ≤ 18384950372513^3751*500000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227846687 500000000 18384950372513 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3882926981/10000000000 : ℝ)^4775 ≤ (5998355573707/20000000000000 : ℝ)^3751 := by
    have hnat : (3882926981 : ℕ)^4775*20000000000000^3751 ≤ 5998355573707^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3882926981 10000000000 5998355573707 20000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4209434019/10000000000 : ℝ), (227846687/500000000 : ℝ), (3882926981/10000000000 : ℝ)] ![(3323832137089/10000000000000 : ℝ), (18384950372513/50000000000000 : ℝ), (5998355573707/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4209434019/10000000000 : ℝ)|^4775 ≤ (3323832137089/10000000000000 : ℝ)^3751
        have hw : |(4209434019/10000000000 : ℝ)|=(4209434019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(227846687/500000000 : ℝ)|^4775 ≤ (18384950372513/50000000000000 : ℝ)^3751
        have hw : |(227846687/500000000 : ℝ)|=(227846687/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3882926981/10000000000 : ℝ)|^4775 ≤ (5998355573707/20000000000000 : ℝ)^3751
        have hw : |(3882926981/10000000000 : ℝ)|=(3882926981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1614_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43378611/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8173/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10451/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10461/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3267/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8173/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10451/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8173/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10451/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8173/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10451/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8173/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10451/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8173/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10451/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8173/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10451/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10451/100000 : ℝ) ^ (4771/1024 : ℝ) ≤ (538406337433111/20000000000000000000 : ℝ) := by
    have hpowers : (10451/100000 : ℝ)^4771 ≤ (538406337433111/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10451 : ℕ)^4771*20000000000000000000^1024 ≤ 538406337433111^1024*100000^4771 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10451 100000 538406337433111 20000000000000000000 4771 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10451/100000 : ℝ)) (X := (538406337433111/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8173/50000 : ℝ) ^ (4771/1024 : ℝ) ≤ (1352143642341231/6250000000000000000 : ℝ) := by
    have hpowers : (8173/50000 : ℝ)^4771 ≤ (1352143642341231/6250000000000000000 : ℝ)^1024 := by
      have hnat : (8173 : ℕ)^4771*6250000000000000000^1024 ≤ 1352143642341231^1024*50000^4771 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8173 50000 1352143642341231 6250000000000000000 4771 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8173/50000 : ℝ)) (X := (1352143642341231/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000538406337433111/10000000000000000000 : ℝ) ≤ (10000115555739573/10000000000000000 : ℝ) ^ (4771/1024 : ℝ) := by
    have hpowers : (10000538406337433111/10000000000000000000 : ℝ)^1024 ≤ (10000115555739573/10000000000000000 : ℝ)^4771 := by
      have hnat : (10000538406337433111 : ℕ)^1024*10000000000000000^4771 ≤ 10000115555739573^4771*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000538406337433111 10000000000000000000 10000115555739573 10000000000000000 1024 4771 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000115555739573/10000000000000000 : ℝ)) (X := (10000538406337433111/10000000000000000000 : ℝ)) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100024326329964625251/100000000000000000000 : ℝ) ≤ (2500130516572333/2500000000000000 : ℝ) ^ (4771/1024 : ℝ) := by
    have hpowers : (100024326329964625251/100000000000000000000 : ℝ)^1024 ≤ (2500130516572333/2500000000000000 : ℝ)^4771 := by
      have hnat : (100024326329964625251 : ℕ)^1024*2500000000000000^4771 ≤ 2500130516572333^4771*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100024326329964625251 100000000000000000000 2500130516572333 2500000000000000 1024 4771 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500130516572333/2500000000000000 : ℝ)) (X := (100024326329964625251/100000000000000000000 : ℝ)) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3126352143642341231/3125000000000000000 : ℝ) ≤ (10000928576839091/10000000000000000 : ℝ) ^ (4771/1024 : ℝ) := by
    have hpowers : (3126352143642341231/3125000000000000000 : ℝ)^1024 ≤ (10000928576839091/10000000000000000 : ℝ)^4771 := by
      have hnat : (3126352143642341231 : ℕ)^1024*10000000000000000^4771 ≤ 10000928576839091^4771*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126352143642341231 3125000000000000000 10000928576839091 10000000000000000 1024 4771 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000928576839091/10000000000000000 : ℝ)) (X := (3126352143642341231/3125000000000000000 : ℝ)) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(538406337433111/20000000000000000000 : ℝ) ≤ ((58942184317573720217/58950000000000000000 : ℝ)+2*(406510549759/589500000000000 : ℝ)*(10451/100000 : ℝ))^(4771/1024 : ℝ) := by
    rw [show (58942184317573720217/58950000000000000000 : ℝ)+2*(406510549759/589500000000000 : ℝ)*(10451/100000 : ℝ)=(10000115555739573/10000000000000000 : ℝ) by norm_num, show 1+2*(538406337433111/20000000000000000000 : ℝ)=(10000538406337433111/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1352143642341231/6250000000000000000 : ℝ)+(538406337433111/20000000000000000000 : ℝ) ≤ ((58942184317573720217/58950000000000000000 : ℝ)+(406510549759/589500000000000 : ℝ)*((8173/50000 : ℝ)+(10451/100000 : ℝ)))^(4771/1024 : ℝ) := by
    rw [show (58942184317573720217/58950000000000000000 : ℝ)+(406510549759/589500000000000 : ℝ)*((8173/50000 : ℝ)+(10451/100000 : ℝ))=(2500130516572333/2500000000000000 : ℝ) by norm_num, show 1+(1352143642341231/6250000000000000000 : ℝ)+(538406337433111/20000000000000000000 : ℝ)=(100024326329964625251/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1352143642341231/6250000000000000000 : ℝ) ≤ ((58942184317573720217/58950000000000000000 : ℝ)+2*(406510549759/589500000000000 : ℝ)*(8173/50000 : ℝ))^(4771/1024 : ℝ) := by
    rw [show (58942184317573720217/58950000000000000000 : ℝ)+2*(406510549759/589500000000000 : ℝ)*(8173/50000 : ℝ)=(10000928576839091/10000000000000000 : ℝ) by norm_num, show 1+2*(1352143642341231/6250000000000000000 : ℝ)=(3126352143642341231/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (58942184317573720217/58950000000000000000 : ℝ)*(X 1 0+X 2 0)+(406510549759/589500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4771/1024 : ℝ)) (lo := (10451/100000 : ℝ)) (hi := (8173/50000 : ℝ)) (c := (58942184317573720217/58950000000000000000 : ℝ)) (alpha := (406510549759/589500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (58942184317573720217/58950000000000000000 : ℝ)*(X 0 1+X 2 1)+(406510549759/589500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4771/1024 : ℝ)) (lo := (10451/100000 : ℝ)) (hi := (8173/50000 : ℝ)) (c := (58942184317573720217/58950000000000000000 : ℝ)) (alpha := (406510549759/589500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (58942184317573720217/58950000000000000000 : ℝ)*(X 0 2+X 1 2)+(406510549759/589500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4771/1024 : ℝ)) (lo := (10451/100000 : ℝ)) (hi := (8173/50000 : ℝ)) (c := (58942184317573720217/58950000000000000000 : ℝ)) (alpha := (406510549759/589500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-847134033/5000000000 : ℝ)*X 0 0+(5458199257/10000000000 : ℝ)*X 0 1+(2590604361/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352988953/10000000000 : ℝ)*X 1 0+(-918535549/5000000000 : ℝ)*X 1 1+(5181208721/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338247237/2500000000 : ℝ)*X 2 0+(5181208719/10000000000 : ℝ)*X 2 1+(-367414221/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4209262139/10000000000 : ℝ)*X 0 0+(3877780283/10000000000 : ℝ)*X 0 1+(2281013461/5000000000 : ℝ)*X 0 2+(4209262139/10000000000 : ℝ)*X 1 0+(3877780283/10000000000 : ℝ)*X 1 1+(2281013461/5000000000 : ℝ)*X 1 2+(4209262139/10000000000 : ℝ)*X 2 0+(3877780283/10000000000 : ℝ)*X 2 1+(2281013461/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-423584407/2500000000 : ℝ)*X 0 0+(2591635239/5000000000 : ℝ)*X 0 1+(1364028961/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1055875009/2000000000 : ℝ)*X 1 0+(-781082023/5000000000 : ℝ)*X 1 1+(54561159/100000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2639687567/5000000000 : ℝ)*X 2 0+(1091223177/2000000000 : ℝ)*X 2 1+(-781081971/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4209434019/10000000000 : ℝ)*X 0 0+(227846687/500000000 : ℝ)*X 0 1+(3882926981/10000000000 : ℝ)*X 0 2+(4209434019/10000000000 : ℝ)*X 1 0+(227846687/500000000 : ℝ)*X 1 1+(3882926981/10000000000 : ℝ)*X 1 2+(4209434019/10000000000 : ℝ)*X 2 0+(227846687/500000000 : ℝ)*X 2 1+(3882926981/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (893648255616516166052158279/196500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (379697361/50000000000000 : ℝ)*(base19) + (715421809/100000000000000 : ℝ)*(base23) + (21733527/100000000000000 : ℝ)*(lower2) + (114410451/100000000000000 : ℝ)*(upper3) + (78254833/100000000000000 : ℝ)*(upper5) + (507171940331713/20000000000000 : ℝ)*(major0) + (507171940331713/20000000000000 : ℝ)*(major1) + (507171940331713/20000000000000 : ℝ)*(major2) + (3610241177563499/100000000000000 : ℝ)*(sp0) + (225640597157929/6250000000000 : ℝ)*(sp1) + (1805124799249889/50000000000000 : ℝ)*(sp2) + (146146491484319/10000000000000 : ℝ)*(sp3) + (1142044761/12500000000000 : ℝ)*(sp4) + (502869759/12500000000000 : ℝ)*(sp7) + (730734468900631/50000000000000 : ℝ)*(f.failure) + (3610250313921587/100000000000000 : ℝ)*(f.sum) + (36302844731933/5895000000000000000000000000 : ℝ)*base66 + (3601812373416013907/393000000000000000000000000000000 : ℝ)*base67 + (23993052548986093/393000000000000000000000000000000 : ℝ)*base70 + (2050621796907013907/393000000000000000000000000000000 : ℝ)*base71 + (13515689453857/5895000000000000000000000000 : ℝ)*base73 + (3645213564609013907/393000000000000000000000000000000 : ℝ)*base75 + (132498777171013907/393000000000000000000000000000000 : ℝ)*base77 + (255136030058986093/393000000000000000000000000000000 : ℝ)*base80 + (19933670877023/5895000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (7303541/1250000000000000000000 : ℝ)*base89 + (7303541/1250000000000000000000 : ℝ)*base91 + (7303541/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (94197413277582571640676691/10234375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (161119203/12500000000000 : ℝ)*(base19) + (1488457141/100000000000000 : ℝ)*(base23) + (84165839/20000000000000 : ℝ)*(lower1) + (741523/400000000000 : ℝ)*(upper3) + (54162627/100000000000000 : ℝ)*(lower4) + (197663733/100000000000000 : ℝ)*(upper5) + (160897582095881/6250000000000 : ℝ)*(major0) + (160897582095881/6250000000000 : ℝ)*(major1) + (160897582095881/6250000000000 : ℝ)*(major2) + (1259526319/50000000000000 : ℝ)*(sp2) + (146602563959041/4000000000000 : ℝ)*(sp4) + (286333032033/7812500000 : ℝ)*(sp5) + (1832530045733123/50000000000000 : ℝ)*(sp6) + (1483658221291419/100000000000000 : ℝ)*(sp7) + (1483658221291419/100000000000000 : ℝ)*(f.failure) + (146602563959041/4000000000000 : ℝ)*(f.sum) + (60519330739889/29475000000000000000000000000 : ℝ)*base65 + (1625070597977717059/122812500000000000000000000000000 : ℝ)*base67 + (750946595572404559/122812500000000000000000000000000 : ℝ)*base69 + (4655957343995529559/122812500000000000000000000000000 : ℝ)*base71 + (29462549569841/7368750000000000000000000000 : ℝ)*base73 + (700392567146345441/122812500000000000000000000000000 : ℝ)*base76 + (857862416281779559/122812500000000000000000000000000 : ℝ)*base77 + (525262740657092059/122812500000000000000000000000000 : ℝ)*base79 + (30462639964289/29475000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (17560991/2500000000000000000000 : ℝ)*base90 + (17560991/2500000000000000000000 : ℝ)*base92 + (17560991/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1614_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43378611/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8173/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10451/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10461/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3267/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1614_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1614_s5_0 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1694276793/10000000000 : ℝ)*x 0 + (1091631109/2000000000 : ℝ)*x 1 + (1295311657/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1694276793/10000000000 : ℝ)^4775 ≤ (5217612538041/50000000000000 : ℝ)^3751 := by
    have hnat : (1694276793 : ℕ)^4775*50000000000000^3751 ≤ 5217612538041^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1694276793 10000000000 5217612538041 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1091631109/2000000000 : ℝ)^4775 ≤ (9253180816287/20000000000000 : ℝ)^3751 := by
    have hnat : (1091631109 : ℕ)^4775*20000000000000^3751 ≤ 9253180816287^3751*2000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091631109 2000000000 9253180816287 20000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295311657/2500000000 : ℝ)^4775 ≤ (21649435411017/50000000000000 : ℝ)^3751 := by
    have hnat : (1295311657 : ℕ)^4775*50000000000000^3751 ≤ 21649435411017^3751*2500000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295311657 2500000000 21649435411017 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1694276793/10000000000 : ℝ), (1091631109/2000000000 : ℝ), (1295311657/2500000000 : ℝ)] ![(5217612538041/50000000000000 : ℝ), (9253180816287/20000000000000 : ℝ), (21649435411017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1694276793/10000000000 : ℝ)|^4775 ≤ (5217612538041/50000000000000 : ℝ)^3751
        have hw : |(-1694276793/10000000000 : ℝ)|=(1694276793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1091631109/2000000000 : ℝ)|^4775 ≤ (9253180816287/20000000000000 : ℝ)^3751
        have hw : |(1091631109/2000000000 : ℝ)|=(1091631109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295311657/2500000000 : ℝ)|^4775 ≤ (21649435411017/50000000000000 : ℝ)^3751
        have hw : |(1295311657/2500000000 : ℝ)|=(1295311657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s5_1 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669122149/1250000000 : ℝ)*x 0 + (-1837036103/10000000000 : ℝ)*x 1 + (2590623477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669122149/1250000000 : ℝ)^4775 ≤ (45133976598209/100000000000000 : ℝ)^3751 := by
    have hnat : (669122149 : ℕ)^4775*100000000000000^3751 ≤ 45133976598209^3751*1250000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669122149 1250000000 45133976598209 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1837036103/10000000000 : ℝ)^4775 ≤ (11567149096107/100000000000000 : ℝ)^3751 := by
    have hnat : (1837036103 : ℕ)^4775*100000000000000^3751 ≤ 11567149096107^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1837036103 10000000000 11567149096107 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590623477/5000000000 : ℝ)^4775 ≤ (43298874290091/100000000000000 : ℝ)^3751 := by
    have hnat : (2590623477 : ℕ)^4775*100000000000000^3751 ≤ 43298874290091^3751*5000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590623477 5000000000 43298874290091 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669122149/1250000000 : ℝ), (-1837036103/10000000000 : ℝ), (2590623477/5000000000 : ℝ)] ![(45133976598209/100000000000000 : ℝ), (11567149096107/100000000000000 : ℝ), (43298874290091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669122149/1250000000 : ℝ)|^4775 ≤ (45133976598209/100000000000000 : ℝ)^3751
        have hw : |(669122149/1250000000 : ℝ)|=(669122149/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1837036103/10000000000 : ℝ)|^4775 ≤ (11567149096107/100000000000000 : ℝ)^3751
        have hw : |(-1837036103/10000000000 : ℝ)|=(1837036103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590623477/5000000000 : ℝ)|^4775 ≤ (43298874290091/100000000000000 : ℝ)^3751
        have hw : |(2590623477/5000000000 : ℝ)|=(2590623477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s5_2 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352977119/10000000000 : ℝ)*x 0 + (1036249389/2000000000 : ℝ)*x 1 + (-459259053/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352977119/10000000000 : ℝ)^4775 ≤ (11283493953669/25000000000000 : ℝ)^3751 := by
    have hnat : (5352977119 : ℕ)^4775*25000000000000^3751 ≤ 11283493953669^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352977119 10000000000 11283493953669 25000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036249389/2000000000 : ℝ)^4775 ≤ (43298874194347/100000000000000 : ℝ)^3751 := by
    have hnat : (1036249389 : ℕ)^4775*100000000000000^3751 ≤ 43298874194347^3751*2000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036249389 2000000000 43298874194347 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (459259053/2500000000 : ℝ)^4775 ≤ (5783574984903/50000000000000 : ℝ)^3751 := by
    have hnat : (459259053 : ℕ)^4775*50000000000000^3751 ≤ 5783574984903^3751*2500000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      459259053 2500000000 5783574984903 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352977119/10000000000 : ℝ), (1036249389/2000000000 : ℝ), (-459259053/2500000000 : ℝ)] ![(11283493953669/25000000000000 : ℝ), (43298874194347/100000000000000 : ℝ), (5783574984903/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352977119/10000000000 : ℝ)|^4775 ≤ (11283493953669/25000000000000 : ℝ)^3751
        have hw : |(5352977119/10000000000 : ℝ)|=(5352977119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036249389/2000000000 : ℝ)|^4775 ≤ (43298874194347/100000000000000 : ℝ)^3751
        have hw : |(1036249389/2000000000 : ℝ)|=(1036249389/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-459259053/2500000000 : ℝ)|^4775 ≤ (5783574984903/50000000000000 : ℝ)^3751
        have hw : |(-459259053/2500000000 : ℝ)|=(459259053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s5_3 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1052316891/2500000000 : ℝ)*x 0 + (3877880373/10000000000 : ℝ)*x 1 + (2280962933/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052316891/2500000000 : ℝ)^4775 ≤ (33236648215839/100000000000000 : ℝ)^3751 := by
    have hnat : (1052316891 : ℕ)^4775*100000000000000^3751 ≤ 33236648215839^3751*2500000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052316891 2500000000 33236648215839 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3877880373/10000000000 : ℝ)^4775 ≤ (14971082645301/50000000000000 : ℝ)^3751 := by
    have hnat : (3877880373 : ℕ)^4775*50000000000000^3751 ≤ 14971082645301^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3877880373 10000000000 14971082645301 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2280962933/5000000000 : ℝ)^4775 ≤ (7364237294327/20000000000000 : ℝ)^3751 := by
    have hnat : (2280962933 : ℕ)^4775*20000000000000^3751 ≤ 7364237294327^3751*5000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2280962933 5000000000 7364237294327 20000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052316891/2500000000 : ℝ), (3877880373/10000000000 : ℝ), (2280962933/5000000000 : ℝ)] ![(33236648215839/100000000000000 : ℝ), (14971082645301/50000000000000 : ℝ), (7364237294327/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052316891/2500000000 : ℝ)|^4775 ≤ (33236648215839/100000000000000 : ℝ)^3751
        have hw : |(1052316891/2500000000 : ℝ)|=(1052316891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3877880373/10000000000 : ℝ)|^4775 ≤ (14971082645301/50000000000000 : ℝ)^3751
        have hw : |(3877880373/10000000000 : ℝ)|=(3877880373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2280962933/5000000000 : ℝ)|^4775 ≤ (7364237294327/20000000000000 : ℝ)^3751
        have hw : |(2280962933/5000000000 : ℝ)|=(2280962933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s5_4 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-423586543/2500000000 : ℝ)*x 0 + (5183307211/10000000000 : ℝ)*x 1 + (5456073413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (423586543/2500000000 : ℝ)^4775 ≤ (2087153809037/20000000000000 : ℝ)^3751 := by
    have hnat : (423586543 : ℕ)^4775*20000000000000^3751 ≤ 2087153809037^3751*2500000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423586543 2500000000 2087153809037 20000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5183307211/10000000000 : ℝ)^4775 ≤ (43320792929501/100000000000000 : ℝ)^3751 := by
    have hnat : (5183307211 : ℕ)^4775*100000000000000^3751 ≤ 43320792929501^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5183307211 10000000000 43320792929501 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5456073413/10000000000 : ℝ)^4775 ≤ (46243438011859/100000000000000 : ℝ)^3751 := by
    have hnat : (5456073413 : ℕ)^4775*100000000000000^3751 ≤ 46243438011859^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456073413 10000000000 46243438011859 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-423586543/2500000000 : ℝ), (5183307211/10000000000 : ℝ), (5456073413/10000000000 : ℝ)] ![(2087153809037/20000000000000 : ℝ), (43320792929501/100000000000000 : ℝ), (46243438011859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-423586543/2500000000 : ℝ)|^4775 ≤ (2087153809037/20000000000000 : ℝ)^3751
        have hw : |(-423586543/2500000000 : ℝ)|=(423586543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5183307211/10000000000 : ℝ)|^4775 ≤ (43320792929501/100000000000000 : ℝ)^3751
        have hw : |(5183307211/10000000000 : ℝ)|=(5183307211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5456073413/10000000000 : ℝ)|^4775 ≤ (46243438011859/100000000000000 : ℝ)^3751
        have hw : |(5456073413/10000000000 : ℝ)|=(5456073413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s5_5 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (21117541/40000000 : ℝ)*x 0 + (-781104827/5000000000 : ℝ)*x 1 + (5456073369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21117541/40000000 : ℝ)^4775 ≤ (44345577155221/100000000000000 : ℝ)^3751 := by
    have hnat : (21117541 : ℕ)^4775*100000000000000^3751 ≤ 44345577155221^3751*40000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21117541 40000000 44345577155221 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (781104827/5000000000 : ℝ)^4775 ≤ (4705492645783/50000000000000 : ℝ)^3751 := by
    have hnat : (781104827 : ℕ)^4775*50000000000000^3751 ≤ 4705492645783^3751*5000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      781104827 5000000000 4705492645783 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5456073369/10000000000 : ℝ)^4775 ≤ (46243437537127/100000000000000 : ℝ)^3751 := by
    have hnat : (5456073369 : ℕ)^4775*100000000000000^3751 ≤ 46243437537127^3751*10000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5456073369 10000000000 46243437537127 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21117541/40000000 : ℝ), (-781104827/5000000000 : ℝ), (5456073369/10000000000 : ℝ)] ![(44345577155221/100000000000000 : ℝ), (4705492645783/50000000000000 : ℝ), (46243437537127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21117541/40000000 : ℝ)|^4775 ≤ (44345577155221/100000000000000 : ℝ)^3751
        have hw : |(21117541/40000000 : ℝ)|=(21117541/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-781104827/5000000000 : ℝ)|^4775 ≤ (4705492645783/50000000000000 : ℝ)^3751
        have hw : |(-781104827/5000000000 : ℝ)|=(781104827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5456073369/10000000000 : ℝ)|^4775 ≤ (46243437537127/100000000000000 : ℝ)^3751
        have hw : |(5456073369/10000000000 : ℝ)|=(5456073369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s5_6 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639692663/5000000000 : ℝ)*x 0 + (2728036657/5000000000 : ℝ)*x 1 + (-781104813/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639692663/5000000000 : ℝ)^4775 ≤ (44345577967877/100000000000000 : ℝ)^3751 := by
    have hnat : (2639692663 : ℕ)^4775*100000000000000^3751 ≤ 44345577967877^3751*5000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639692663 5000000000 44345577967877 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2728036657/5000000000 : ℝ)^4775 ≤ (46243436943711/100000000000000 : ℝ)^3751 := by
    have hnat : (2728036657 : ℕ)^4775*100000000000000^3751 ≤ 46243436943711^3751*5000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2728036657 5000000000 46243436943711 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (781104813/5000000000 : ℝ)^4775 ≤ (4705492538421/50000000000000 : ℝ)^3751 := by
    have hnat : (781104813 : ℕ)^4775*50000000000000^3751 ≤ 4705492538421^3751*5000000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      781104813 5000000000 4705492538421 50000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639692663/5000000000 : ℝ), (2728036657/5000000000 : ℝ), (-781104813/5000000000 : ℝ)] ![(44345577967877/100000000000000 : ℝ), (46243436943711/100000000000000 : ℝ), (4705492538421/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639692663/5000000000 : ℝ)|^4775 ≤ (44345577967877/100000000000000 : ℝ)^3751
        have hw : |(2639692663/5000000000 : ℝ)|=(2639692663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2728036657/5000000000 : ℝ)|^4775 ≤ (46243436943711/100000000000000 : ℝ)^3751
        have hw : |(2728036657/5000000000 : ℝ)|=(2728036657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-781104813/5000000000 : ℝ)|^4775 ≤ (4705492538421/50000000000000 : ℝ)^3751
        have hw : |(-781104813/5000000000 : ℝ)|=(781104813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1614_s5_7 (p : ℝ) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (131544987/312500000 : ℝ)*x 0 + (91136703/200000000 : ℝ)*x 1 + (970756071/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (131544987/312500000 : ℝ)^4775 ≤ (3323837730889/10000000000000 : ℝ)^3751 := by
    have hnat : (131544987 : ℕ)^4775*10000000000000^3751 ≤ 3323837730889^3751*312500000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131544987 312500000 3323837730889 10000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (91136703/200000000 : ℝ)^4775 ≤ (36768888052419/100000000000000 : ℝ)^3751 := by
    have hnat : (91136703 : ℕ)^4775*100000000000000^3751 ≤ 36768888052419^3751*200000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91136703 200000000 36768888052419 100000000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (970756071/2500000000 : ℝ)^4775 ≤ (937272956729/3125000000000 : ℝ)^3751 := by
    have hnat : (970756071 : ℕ)^4775*3125000000000^3751 ≤ 937272956729^3751*2500000000^4775 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      970756071 2500000000 937272956729 3125000000000 4775 3751 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4775/1024 : ℝ)) 4775 3751 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(131544987/312500000 : ℝ), (91136703/200000000 : ℝ), (970756071/2500000000 : ℝ)] ![(3323837730889/10000000000000 : ℝ), (36768888052419/100000000000000 : ℝ), (937272956729/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(131544987/312500000 : ℝ)|^4775 ≤ (3323837730889/10000000000000 : ℝ)^3751
        have hw : |(131544987/312500000 : ℝ)|=(131544987/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(91136703/200000000 : ℝ)|^4775 ≤ (36768888052419/100000000000000 : ℝ)^3751
        have hw : |(91136703/200000000 : ℝ)|=(91136703/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(970756071/2500000000 : ℝ)|^4775 ≤ (937272956729/3125000000000 : ℝ)^3751
        have hw : |(970756071/2500000000 : ℝ)|=(970756071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1614_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43378611/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3267/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10461/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5231/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8167/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3267/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10461/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3267/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10461/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3267/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10461/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3267/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10461/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3267/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10461/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3267/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10461/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10461/100000 : ℝ) ^ (4771/1024 : ℝ) ≤ (540810822289767/20000000000000000000 : ℝ) := by
    have hpowers : (10461/100000 : ℝ)^4771 ≤ (540810822289767/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10461 : ℕ)^4771*20000000000000000000^1024 ≤ 540810822289767^1024*100000^4771 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10461 100000 540810822289767 20000000000000000000 4771 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10461/100000 : ℝ)) (X := (540810822289767/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3267/20000 : ℝ) ^ (4771/1024 : ℝ) ≤ (10783274962186241/50000000000000000000 : ℝ) := by
    have hpowers : (3267/20000 : ℝ)^4771 ≤ (10783274962186241/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3267 : ℕ)^4771*50000000000000000000^1024 ≤ 10783274962186241^1024*20000^4771 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3267 20000 10783274962186241 50000000000000000000 4771 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3267/20000 : ℝ)) (X := (10783274962186241/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000540810822289767/10000000000000000000 : ℝ) ≤ (1250014508974053/1250000000000000 : ℝ) ^ (4771/1024 : ℝ) := by
    have hpowers : (10000540810822289767/10000000000000000000 : ℝ)^1024 ≤ (1250014508974053/1250000000000000 : ℝ)^4771 := by
      have hnat : (10000540810822289767 : ℕ)^1024*1250000000000000^4771 ≤ 1250014508974053^4771*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000540810822289767 10000000000000000000 1250014508974053 1250000000000000 1024 4771 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250014508974053/1250000000000000 : ℝ)) (X := (10000540810822289767/10000000000000000000 : ℝ)) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100024270604035821317/100000000000000000000 : ℝ) ≤ (5000260435235801/5000000000000000 : ℝ) ^ (4771/1024 : ℝ) := by
    have hpowers : (100024270604035821317/100000000000000000000 : ℝ)^1024 ≤ (5000260435235801/5000000000000000 : ℝ)^4771 := by
      have hnat : (100024270604035821317 : ℕ)^1024*5000000000000000^4771 ≤ 5000260435235801^4771*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100024270604035821317 100000000000000000000 5000260435235801 5000000000000000 1024 4771 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000260435235801/5000000000000000 : ℝ)) (X := (100024270604035821317/100000000000000000000 : ℝ)) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010783274962186241/25000000000000000000 : ℝ) ≤ (500046283457539/500000000000000 : ℝ) ^ (4771/1024 : ℝ) := by
    have hpowers : (25010783274962186241/25000000000000000000 : ℝ)^1024 ≤ (500046283457539/500000000000000 : ℝ)^4771 := by
      have hnat : (25010783274962186241 : ℕ)^1024*500000000000000^4771 ≤ 500046283457539^4771*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010783274962186241 25000000000000000000 500046283457539 500000000000000 1024 4771 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500046283457539/500000000000000 : ℝ)) (X := (25010783274962186241/25000000000000000000 : ℝ)) (by norm_num) 4771 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(540810822289767/20000000000000000000 : ℝ) ≤ ((88988200920822631/89000000000000000 : ℝ)+2*(202399339589/293700000000000 : ℝ)*(10461/100000 : ℝ))^(4771/1024 : ℝ) := by
    rw [show (88988200920822631/89000000000000000 : ℝ)+2*(202399339589/293700000000000 : ℝ)*(10461/100000 : ℝ)=(1250014508974053/1250000000000000 : ℝ) by norm_num, show 1+2*(540810822289767/20000000000000000000 : ℝ)=(10000540810822289767/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10783274962186241/50000000000000000000 : ℝ)+(540810822289767/20000000000000000000 : ℝ) ≤ ((88988200920822631/89000000000000000 : ℝ)+(202399339589/293700000000000 : ℝ)*((3267/20000 : ℝ)+(10461/100000 : ℝ)))^(4771/1024 : ℝ) := by
    rw [show (88988200920822631/89000000000000000 : ℝ)+(202399339589/293700000000000 : ℝ)*((3267/20000 : ℝ)+(10461/100000 : ℝ))=(5000260435235801/5000000000000000 : ℝ) by norm_num, show 1+(10783274962186241/50000000000000000000 : ℝ)+(540810822289767/20000000000000000000 : ℝ)=(100024270604035821317/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10783274962186241/50000000000000000000 : ℝ) ≤ ((88988200920822631/89000000000000000 : ℝ)+2*(202399339589/293700000000000 : ℝ)*(3267/20000 : ℝ))^(4771/1024 : ℝ) := by
    rw [show (88988200920822631/89000000000000000 : ℝ)+2*(202399339589/293700000000000 : ℝ)*(3267/20000 : ℝ)=(500046283457539/500000000000000 : ℝ) by norm_num, show 1+2*(10783274962186241/50000000000000000000 : ℝ)=(25010783274962186241/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (88988200920822631/89000000000000000 : ℝ)*(X 1 0+X 2 0)+(202399339589/293700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4771/1024 : ℝ)) (lo := (10461/100000 : ℝ)) (hi := (3267/20000 : ℝ)) (c := (88988200920822631/89000000000000000 : ℝ)) (alpha := (202399339589/293700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (88988200920822631/89000000000000000 : ℝ)*(X 0 1+X 2 1)+(202399339589/293700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4771/1024 : ℝ)) (lo := (10461/100000 : ℝ)) (hi := (3267/20000 : ℝ)) (c := (88988200920822631/89000000000000000 : ℝ)) (alpha := (202399339589/293700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (88988200920822631/89000000000000000 : ℝ)*(X 0 2+X 1 2)+(202399339589/293700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4771/1024 : ℝ)) (lo := (10461/100000 : ℝ)) (hi := (3267/20000 : ℝ)) (c := (88988200920822631/89000000000000000 : ℝ)) (alpha := (202399339589/293700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1694276793/10000000000 : ℝ)*X 0 0+(1091631109/2000000000 : ℝ)*X 0 1+(1295311657/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669122149/1250000000 : ℝ)*X 1 0+(-1837036103/10000000000 : ℝ)*X 1 1+(2590623477/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5352977119/10000000000 : ℝ)*X 2 0+(1036249389/2000000000 : ℝ)*X 2 1+(-459259053/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1052316891/2500000000 : ℝ)*X 0 0+(3877880373/10000000000 : ℝ)*X 0 1+(2280962933/5000000000 : ℝ)*X 0 2+(1052316891/2500000000 : ℝ)*X 1 0+(3877880373/10000000000 : ℝ)*X 1 1+(2280962933/5000000000 : ℝ)*X 1 2+(1052316891/2500000000 : ℝ)*X 2 0+(3877880373/10000000000 : ℝ)*X 2 1+(2280962933/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-423586543/2500000000 : ℝ)*X 0 0+(5183307211/10000000000 : ℝ)*X 0 1+(5456073413/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((21117541/40000000 : ℝ)*X 1 0+(-781104827/5000000000 : ℝ)*X 1 1+(5456073369/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2639692663/5000000000 : ℝ)*X 2 0+(2728036657/5000000000 : ℝ)*X 2 1+(-781104813/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((131544987/312500000 : ℝ)*X 0 0+(91136703/200000000 : ℝ)*X 0 1+(970756071/2500000000 : ℝ)*X 0 2+(131544987/312500000 : ℝ)*X 1 0+(91136703/200000000 : ℝ)*X 1 1+(970756071/2500000000 : ℝ)*X 1 2+(131544987/312500000 : ℝ)*X 2 0+(91136703/200000000 : ℝ)*X 2 1+(970756071/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1614_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6454135562135766444273/2447500000000000000000000000 : ℝ) := by norm_num
    linear_combination (21880021/5000000000000 : ℝ)*(base19) + (67138213/20000000000000 : ℝ)*(base23) + (20749339/100000000000000 : ℝ)*(upper2) + (25300303/20000000000000 : ℝ)*(upper3) + (24469301/50000000000000 : ℝ)*(upper4) + (1268303061611329/50000000000000 : ℝ)*(major0) + (1268303061611329/50000000000000 : ℝ)*(major1) + (1268303061611329/50000000000000 : ℝ)*(major2) + (1805652844407889/50000000000000 : ℝ)*(sp0) + (1805656302398621/50000000000000 : ℝ)*(sp1) + (902828176676649/25000000000000 : ℝ)*(sp2) + (146189456058987/10000000000000 : ℝ)*(sp3) + (1838395471/25000000000000 : ℝ)*(sp4) + (2277778357/50000000000000 : ℝ)*(sp7) + (1461899116146583/100000000000000 : ℝ)*(f.failure) + (1805656521198831/50000000000000 : ℝ)*(f.sum) + (16713293142857/3671250000000000000000000000 : ℝ)*base66 + (443970075875432233/146850000000000000000000000000000 : ℝ)*base68 + (526307949832232233/146850000000000000000000000000000 : ℝ)*base70 + (480150241101032233/146850000000000000000000000000000 : ℝ)*base72 + (34862302243489/7342500000000000000000000000 : ℝ)*base74 + (763981617072567767/146850000000000000000000000000000 : ℝ)*base75 + (984844088147967767/146850000000000000000000000000000 : ℝ)*base77 + (680020604485467767/146850000000000000000000000000000 : ℝ)*base79 + (63204904105789/7342500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (7063787/2500000000000000000000 : ℝ)*base90 + (7063787/2500000000000000000000 : ℝ)*base92 + (7063787/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38729328407855742171717/4895000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1253741853/100000000000000 : ℝ)*(base19) + (2265577/160000000000 : ℝ)*(base23) + (413264223/100000000000000 : ℝ)*(lower1) + (140295897/100000000000000 : ℝ)*(upper3) + (26429469/50000000000000 : ℝ)*(lower4) + (196226147/100000000000000 : ℝ)*(upper5) + (643777313704803/25000000000000 : ℝ)*(major0) + (643777313704803/25000000000000 : ℝ)*(major1) + (643777313704803/25000000000000 : ℝ)*(major2) + (670352243/100000000000000 : ℝ)*(sp2) + (7160408145353/195312500000 : ℝ)*(sp4) + (3666127716678883/100000000000000 : ℝ)*(sp5) + (916531721020717/25000000000000 : ℝ)*(sp6) + (371022318870931/25000000000000 : ℝ)*(sp7) + (371022318870931/25000000000000 : ℝ)*(f.failure) + (7160408145353/195312500000 : ℝ)*(f.sum) + (31141092869/1223750000000000000000000000 : ℝ)*base65 + (141726783870946377/24475000000000000000000000000000 : ℝ)*base68 + (277078910734746377/24475000000000000000000000000000 : ℝ)*base70 + (3028006464230803623/24475000000000000000000000000000 : ℝ)*base71 + (10700943280173/2447500000000000000000000000 : ℝ)*base73 + (3203003357908771377/24475000000000000000000000000000 : ℝ)*base76 + (70451205601678623/24475000000000000000000000000000 : ℝ)*base77 + (54946853921828623/24475000000000000000000000000000 : ℝ)*base79 + (388027203831/76484375000000000000000000 : ℝ)*base82 + (56841/625000000000000000000 : ℝ)*base89 + (56841/625000000000000000000 : ℝ)*base91 + (56841/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1614_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43378611/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3267/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10461/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5231/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8167/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1614_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1614_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43378611/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16477/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10333/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5231/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8167/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1614_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1614_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1614_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4771/1024 : ℝ) ≤ p) (hpb : p ≤ (4775/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (43378611/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16477/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10333/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5231/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8167/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1614_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
