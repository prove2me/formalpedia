-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1606_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:50:19.125486+00:00
-- url     : https://prove2.me/submissions/35cd1553-3b50-4648-a040-fa9ce89ed1d2

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
theorem support_rectangle_w1606_s3_0 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-857136079/5000000000 : ℝ)*x 0 + (2730660477/5000000000 : ℝ)*x 1 + (1294963229/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (857136079/5000000000 : ℝ)^4743 ≤ (10548461578197/100000000000000 : ℝ)^3719 := by
    have hnat : (857136079 : ℕ)^4743*100000000000000^3719 ≤ 10548461578197^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857136079 5000000000 10548461578197 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2730660477/5000000000 : ℝ)^4743 ≤ (11558580794223/25000000000000 : ℝ)^3719 := by
    have hnat : (2730660477 : ℕ)^4743*25000000000000^3719 ≤ 11558580794223^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2730660477 5000000000 11558580794223 25000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1294963229/2500000000 : ℝ)^4743 ≤ (1350537975697/3125000000000 : ℝ)^3719 := by
    have hnat : (1294963229 : ℕ)^4743*3125000000000^3719 ≤ 1350537975697^3719*2500000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1294963229 2500000000 1350537975697 3125000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-857136079/5000000000 : ℝ), (2730660477/5000000000 : ℝ), (1294963229/2500000000 : ℝ)] ![(10548461578197/100000000000000 : ℝ), (11558580794223/25000000000000 : ℝ), (1350537975697/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-857136079/5000000000 : ℝ)|^4743 ≤ (10548461578197/100000000000000 : ℝ)^3719
        have hw : |(-857136079/5000000000 : ℝ)|=(857136079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2730660477/5000000000 : ℝ)|^4743 ≤ (11558580794223/25000000000000 : ℝ)^3719
        have hw : |(2730660477/5000000000 : ℝ)|=(2730660477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1294963229/2500000000 : ℝ)|^4743 ≤ (1350537975697/3125000000000 : ℝ)^3719
        have hw : |(1294963229/2500000000 : ℝ)|=(1294963229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s3_1 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070859801/2000000000 : ℝ)*x 0 + (-1859455193/10000000000 : ℝ)*x 1 + (5179852929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070859801/2000000000 : ℝ)^4743 ≤ (5635245538101/12500000000000 : ℝ)^3719 := by
    have hnat : (1070859801 : ℕ)^4743*12500000000000^3719 ≤ 5635245538101^3719*2000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070859801 2000000000 5635245538101 12500000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1859455193/10000000000 : ℝ)^4743 ≤ (9141265881/78125000000 : ℝ)^3719 := by
    have hnat : (1859455193 : ℕ)^4743*78125000000^3719 ≤ 9141265881^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1859455193 10000000000 9141265881 78125000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5179852929/10000000000 : ℝ)^4743 ≤ (5402151920079/12500000000000 : ℝ)^3719 := by
    have hnat : (5179852929 : ℕ)^4743*12500000000000^3719 ≤ 5402151920079^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5179852929 10000000000 5402151920079 12500000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070859801/2000000000 : ℝ), (-1859455193/10000000000 : ℝ), (5179852929/10000000000 : ℝ)] ![(5635245538101/12500000000000 : ℝ), (9141265881/78125000000 : ℝ), (5402151920079/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070859801/2000000000 : ℝ)|^4743 ≤ (5635245538101/12500000000000 : ℝ)^3719
        have hw : |(1070859801/2000000000 : ℝ)|=(1070859801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1859455193/10000000000 : ℝ)|^4743 ≤ (9141265881/78125000000 : ℝ)^3719
        have hw : |(-1859455193/10000000000 : ℝ)|=(1859455193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5179852929/10000000000 : ℝ)|^4743 ≤ (5402151920079/12500000000000 : ℝ)^3719
        have hw : |(5179852929/10000000000 : ℝ)|=(5179852929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s3_2 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070859803/2000000000 : ℝ)*x 0 + (2589926459/5000000000 : ℝ)*x 1 + (-929727597/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070859803/2000000000 : ℝ)^4743 ≤ (45081964412189/100000000000000 : ℝ)^3719 := by
    have hnat : (1070859803 : ℕ)^4743*100000000000000^3719 ≤ 45081964412189^3719*2000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070859803 2000000000 45081964412189 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2589926459/5000000000 : ℝ)^4743 ≤ (8643443048717/20000000000000 : ℝ)^3719 := by
    have hnat : (2589926459 : ℕ)^4743*20000000000000^3719 ≤ 8643443048717^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589926459 5000000000 8643443048717 20000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (929727597/5000000000 : ℝ)^4743 ≤ (2340164067141/20000000000000 : ℝ)^3719 := by
    have hnat : (929727597 : ℕ)^4743*20000000000000^3719 ≤ 2340164067141^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929727597 5000000000 2340164067141 20000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070859803/2000000000 : ℝ), (2589926459/5000000000 : ℝ), (-929727597/5000000000 : ℝ)] ![(45081964412189/100000000000000 : ℝ), (8643443048717/20000000000000 : ℝ), (2340164067141/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070859803/2000000000 : ℝ)|^4743 ≤ (45081964412189/100000000000000 : ℝ)^3719
        have hw : |(1070859803/2000000000 : ℝ)|=(1070859803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2589926459/5000000000 : ℝ)|^4743 ≤ (8643443048717/20000000000000 : ℝ)^3719
        have hw : |(2589926459/5000000000 : ℝ)|=(2589926459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-929727597/5000000000 : ℝ)|^4743 ≤ (2340164067141/20000000000000 : ℝ)^3719
        have hw : |(-929727597/5000000000 : ℝ)|=(929727597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s3_3 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4215771819/10000000000 : ℝ)*x 0 + (1941318153/5000000000 : ℝ)*x 1 + (4570657677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4215771819/10000000000 : ℝ)^4743 ≤ (6646908320317/20000000000000 : ℝ)^3719 := by
    have hnat : (4215771819 : ℕ)^4743*20000000000000^3719 ≤ 6646908320317^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4215771819 10000000000 6646908320317 20000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1941318153/5000000000 : ℝ)^4743 ≤ (29922349788221/100000000000000 : ℝ)^3719 := by
    have hnat : (1941318153 : ℕ)^4743*100000000000000^3719 ≤ 29922349788221^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1941318153 5000000000 29922349788221 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4570657677/10000000000 : ℝ)^4743 ≤ (36843108588847/100000000000000 : ℝ)^3719 := by
    have hnat : (4570657677 : ℕ)^4743*100000000000000^3719 ≤ 36843108588847^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4570657677 10000000000 36843108588847 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4215771819/10000000000 : ℝ), (1941318153/5000000000 : ℝ), (4570657677/10000000000 : ℝ)] ![(6646908320317/20000000000000 : ℝ), (29922349788221/100000000000000 : ℝ), (36843108588847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4215771819/10000000000 : ℝ)|^4743 ≤ (6646908320317/20000000000000 : ℝ)^3719
        have hw : |(4215771819/10000000000 : ℝ)|=(4215771819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1941318153/5000000000 : ℝ)|^4743 ≤ (29922349788221/100000000000000 : ℝ)^3719
        have hw : |(1941318153/5000000000 : ℝ)|=(1941318153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4570657677/10000000000 : ℝ)|^4743 ≤ (36843108588847/100000000000000 : ℝ)^3719
        have hw : |(4570657677/10000000000 : ℝ)|=(4570657677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s3_4 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-214293/1250000 : ℝ)*x 0 + (5181949519/10000000000 : ℝ)*x 1 + (545920223/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214293/1250000 : ℝ)^4743 ≤ (2637256342001/25000000000000 : ℝ)^3719 := by
    have hnat : (214293 : ℕ)^4743*25000000000000^3719 ≤ 2637256342001^3719*1250000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214293 1250000 2637256342001 25000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5181949519/10000000000 : ℝ)^4743 ≤ (43239525588449/100000000000000 : ℝ)^3719 := by
    have hnat : (5181949519 : ℕ)^4743*100000000000000^3719 ≤ 43239525588449^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181949519 10000000000 43239525588449 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545920223/1000000000 : ℝ)^4743 ≤ (46211449028283/100000000000000 : ℝ)^3719 := by
    have hnat : (545920223 : ℕ)^4743*100000000000000^3719 ≤ 46211449028283^3719*1000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545920223 1000000000 46211449028283 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-214293/1250000 : ℝ), (5181949519/10000000000 : ℝ), (545920223/1000000000 : ℝ)] ![(2637256342001/25000000000000 : ℝ), (43239525588449/100000000000000 : ℝ), (46211449028283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-214293/1250000 : ℝ)|^4743 ≤ (2637256342001/25000000000000 : ℝ)^3719
        have hw : |(-214293/1250000 : ℝ)|=(214293/1250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5181949519/10000000000 : ℝ)|^4743 ≤ (43239525588449/100000000000000 : ℝ)^3719
        have hw : |(5181949519/10000000000 : ℝ)|=(5181949519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(545920223/1000000000 : ℝ)|^4743 ≤ (46211449028283/100000000000000 : ℝ)^3719
        have hw : |(545920223/1000000000 : ℝ)|=(545920223/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s3_5 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (65995027/125000000 : ℝ)*x 0 + (-790053071/5000000000 : ℝ)*x 1 + (682400213/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65995027/125000000 : ℝ)^4743 ≤ (44281408406311/100000000000000 : ℝ)^3719 := by
    have hnat : (65995027 : ℕ)^4743*100000000000000^3719 ≤ 44281408406311^3719*125000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65995027 125000000 44281408406311 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (790053071/5000000000 : ℝ)^4743 ≤ (950714823327/10000000000000 : ℝ)^3719 := by
    have hnat : (790053071 : ℕ)^4743*10000000000000^3719 ≤ 950714823327^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      790053071 5000000000 950714823327 10000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (682400213/1250000000 : ℝ)^4743 ≤ (46211443349791/100000000000000 : ℝ)^3719 := by
    have hnat : (682400213 : ℕ)^4743*100000000000000^3719 ≤ 46211443349791^3719*1250000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682400213 1250000000 46211443349791 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65995027/125000000 : ℝ), (-790053071/5000000000 : ℝ), (682400213/1250000000 : ℝ)] ![(44281408406311/100000000000000 : ℝ), (950714823327/10000000000000 : ℝ), (46211443349791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65995027/125000000 : ℝ)|^4743 ≤ (44281408406311/100000000000000 : ℝ)^3719
        have hw : |(65995027/125000000 : ℝ)|=(65995027/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-790053071/5000000000 : ℝ)|^4743 ≤ (950714823327/10000000000000 : ℝ)^3719
        have hw : |(-790053071/5000000000 : ℝ)|=(790053071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(682400213/1250000000 : ℝ)|^4743 ≤ (46211443349791/100000000000000 : ℝ)^3719
        have hw : |(682400213/1250000000 : ℝ)|=(682400213/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s3_6 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055920267/2000000000 : ℝ)*x 0 + (5459202293/10000000000 : ℝ)*x 1 + (-1580106463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055920267/2000000000 : ℝ)^4743 ≤ (11070349895397/25000000000000 : ℝ)^3719 := by
    have hnat : (1055920267 : ℕ)^4743*25000000000000^3719 ≤ 11070349895397^3719*2000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055920267 2000000000 11070349895397 25000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5459202293/10000000000 : ℝ)^4743 ≤ (46211449708407/100000000000000 : ℝ)^3719 := by
    have hnat : (5459202293 : ℕ)^4743*100000000000000^3719 ≤ 46211449708407^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459202293 10000000000 46211449708407 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1580106463/10000000000 : ℝ)^4743 ≤ (9507150696449/100000000000000 : ℝ)^3719 := by
    have hnat : (1580106463 : ℕ)^4743*100000000000000^3719 ≤ 9507150696449^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1580106463 10000000000 9507150696449 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055920267/2000000000 : ℝ), (5459202293/10000000000 : ℝ), (-1580106463/10000000000 : ℝ)] ![(11070349895397/25000000000000 : ℝ), (46211449708407/100000000000000 : ℝ), (9507150696449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055920267/2000000000 : ℝ)|^4743 ≤ (11070349895397/25000000000000 : ℝ)^3719
        have hw : |(1055920267/2000000000 : ℝ)|=(1055920267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5459202293/10000000000 : ℝ)|^4743 ≤ (46211449708407/100000000000000 : ℝ)^3719
        have hw : |(5459202293/10000000000 : ℝ)|=(5459202293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1580106463/10000000000 : ℝ)|^4743 ≤ (9507150696449/100000000000000 : ℝ)^3719
        have hw : |(-1580106463/10000000000 : ℝ)|=(1580106463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s3_7 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2107973801/5000000000 : ℝ)*x 0 + (4565531801/10000000000 : ℝ)*x 1 + (777563219/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2107973801/5000000000 : ℝ)^4743 ≤ (16618154468353/50000000000000 : ℝ)^3719 := by
    have hnat : (2107973801 : ℕ)^4743*50000000000000^3719 ≤ 16618154468353^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107973801 5000000000 16618154468353 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4565531801/10000000000 : ℝ)^4743 ≤ (36790421338219/100000000000000 : ℝ)^3719 := by
    have hnat : (4565531801 : ℕ)^4743*100000000000000^3719 ≤ 36790421338219^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4565531801 10000000000 36790421338219 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (777563219/2000000000 : ℝ)^4743 ≤ (5994653942091/20000000000000 : ℝ)^3719 := by
    have hnat : (777563219 : ℕ)^4743*20000000000000^3719 ≤ 5994653942091^3719*2000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      777563219 2000000000 5994653942091 20000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2107973801/5000000000 : ℝ), (4565531801/10000000000 : ℝ), (777563219/2000000000 : ℝ)] ![(16618154468353/50000000000000 : ℝ), (36790421338219/100000000000000 : ℝ), (5994653942091/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2107973801/5000000000 : ℝ)|^4743 ≤ (16618154468353/50000000000000 : ℝ)^3719
        have hw : |(2107973801/5000000000 : ℝ)|=(2107973801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4565531801/10000000000 : ℝ)|^4743 ≤ (36790421338219/100000000000000 : ℝ)^3719
        have hw : |(4565531801/10000000000 : ℝ)|=(4565531801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(777563219/2000000000 : ℝ)|^4743 ≤ (5994653942091/20000000000000 : ℝ)^3719
        have hw : |(777563219/2000000000 : ℝ)|=(777563219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1606_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34444033/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16511/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5131/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2599/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8181/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16511/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5131/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16511/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5131/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16511/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5131/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16511/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5131/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16511/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5131/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16511/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5131/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5131/50000 : ℝ) ^ (4739/1024 : ℝ) ≤ (2654918944700751/100000000000000000000 : ℝ) := by
    have hpowers : (5131/50000 : ℝ)^4739 ≤ (2654918944700751/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5131 : ℕ)^4739*100000000000000000000^1024 ≤ 2654918944700751^1024*50000^4739 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5131 50000 2654918944700751 100000000000000000000 4739 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5131/50000 : ℝ)) (X := (2654918944700751/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16511/100000 : ℝ) ^ (4739/1024 : ℝ) ≤ (23983369083535483/100000000000000000000 : ℝ) := by
    have hpowers : (16511/100000 : ℝ)^4739 ≤ (23983369083535483/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16511 : ℕ)^4739*100000000000000000000^1024 ≤ 23983369083535483^1024*100000^4739 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16511 100000 23983369083535483 100000000000000000000 4739 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16511/100000 : ℝ)) (X := (23983369083535483/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002654918944700751/50000000000000000000 : ℝ) ≤ (5000057366119849/5000000000000000 : ℝ) ^ (4739/1024 : ℝ) := by
    have hpowers : (50002654918944700751/50000000000000000000 : ℝ)^1024 ≤ (5000057366119849/5000000000000000 : ℝ)^4739 := by
      have hnat : (50002654918944700751 : ℕ)^1024*5000000000000000^4739 ≤ 5000057366119849^4739*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002654918944700751 50000000000000000000 5000057366119849 5000000000000000 1024 4739 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000057366119849/5000000000000000 : ℝ)) (X := (50002654918944700751/50000000000000000000 : ℝ)) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013319144014118117/50000000000000000000 : ℝ) ≤ (5000287769142177/5000000000000000 : ℝ) ^ (4739/1024 : ℝ) := by
    have hpowers : (50013319144014118117/50000000000000000000 : ℝ)^1024 ≤ (5000287769142177/5000000000000000 : ℝ)^4739 := by
      have hnat : (50013319144014118117 : ℕ)^1024*5000000000000000^4739 ≤ 5000287769142177^4739*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013319144014118117 50000000000000000000 5000287769142177 5000000000000000 1024 4739 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000287769142177/5000000000000000 : ℝ)) (X := (50013319144014118117/50000000000000000000 : ℝ)) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50023983369083535483/50000000000000000000 : ℝ) ≤ (1000103634432901/1000000000000000 : ℝ) ^ (4739/1024 : ℝ) := by
    have hpowers : (50023983369083535483/50000000000000000000 : ℝ)^1024 ≤ (1000103634432901/1000000000000000 : ℝ)^4739 := by
      have hnat : (50023983369083535483 : ℕ)^1024*1000000000000000^4739 ≤ 1000103634432901^4739*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023983369083535483 50000000000000000000 1000103634432901 1000000000000000 1024 4739 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000103634432901/1000000000000000 : ℝ)) (X := (50023983369083535483/50000000000000000000 : ℝ)) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2654918944700751/100000000000000000000 : ℝ) ≤ ((31240629689252676529/31245000000000000000 : ℝ)+2*(28800377791/39056250000000 : ℝ)*(5131/50000 : ℝ))^(4739/1024 : ℝ) := by
    rw [show (31240629689252676529/31245000000000000000 : ℝ)+2*(28800377791/39056250000000 : ℝ)*(5131/50000 : ℝ)=(5000057366119849/5000000000000000 : ℝ) by norm_num, show 1+2*(2654918944700751/100000000000000000000 : ℝ)=(50002654918944700751/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23983369083535483/100000000000000000000 : ℝ)+(2654918944700751/100000000000000000000 : ℝ) ≤ ((31240629689252676529/31245000000000000000 : ℝ)+(28800377791/39056250000000 : ℝ)*((16511/100000 : ℝ)+(5131/50000 : ℝ)))^(4739/1024 : ℝ) := by
    rw [show (31240629689252676529/31245000000000000000 : ℝ)+(28800377791/39056250000000 : ℝ)*((16511/100000 : ℝ)+(5131/50000 : ℝ))=(5000287769142177/5000000000000000 : ℝ) by norm_num, show 1+(23983369083535483/100000000000000000000 : ℝ)+(2654918944700751/100000000000000000000 : ℝ)=(50013319144014118117/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23983369083535483/100000000000000000000 : ℝ) ≤ ((31240629689252676529/31245000000000000000 : ℝ)+2*(28800377791/39056250000000 : ℝ)*(16511/100000 : ℝ))^(4739/1024 : ℝ) := by
    rw [show (31240629689252676529/31245000000000000000 : ℝ)+2*(28800377791/39056250000000 : ℝ)*(16511/100000 : ℝ)=(1000103634432901/1000000000000000 : ℝ) by norm_num, show 1+2*(23983369083535483/100000000000000000000 : ℝ)=(50023983369083535483/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (31240629689252676529/31245000000000000000 : ℝ)*(X 1 0+X 2 0)+(28800377791/39056250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4739/1024 : ℝ)) (lo := (5131/50000 : ℝ)) (hi := (16511/100000 : ℝ)) (c := (31240629689252676529/31245000000000000000 : ℝ)) (alpha := (28800377791/39056250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (31240629689252676529/31245000000000000000 : ℝ)*(X 0 1+X 2 1)+(28800377791/39056250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4739/1024 : ℝ)) (lo := (5131/50000 : ℝ)) (hi := (16511/100000 : ℝ)) (c := (31240629689252676529/31245000000000000000 : ℝ)) (alpha := (28800377791/39056250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (31240629689252676529/31245000000000000000 : ℝ)*(X 0 2+X 1 2)+(28800377791/39056250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4739/1024 : ℝ)) (lo := (5131/50000 : ℝ)) (hi := (16511/100000 : ℝ)) (c := (31240629689252676529/31245000000000000000 : ℝ)) (alpha := (28800377791/39056250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-857136079/5000000000 : ℝ)*X 0 0+(2730660477/5000000000 : ℝ)*X 0 1+(1294963229/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1070859801/2000000000 : ℝ)*X 1 0+(-1859455193/10000000000 : ℝ)*X 1 1+(5179852929/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070859803/2000000000 : ℝ)*X 2 0+(2589926459/5000000000 : ℝ)*X 2 1+(-929727597/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4215771819/10000000000 : ℝ)*X 0 0+(1941318153/5000000000 : ℝ)*X 0 1+(4570657677/10000000000 : ℝ)*X 0 2+(4215771819/10000000000 : ℝ)*X 1 0+(1941318153/5000000000 : ℝ)*X 1 1+(4570657677/10000000000 : ℝ)*X 1 2+(4215771819/10000000000 : ℝ)*X 2 0+(1941318153/5000000000 : ℝ)*X 2 1+(4570657677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-214293/1250000 : ℝ)*X 0 0+(5181949519/10000000000 : ℝ)*X 0 1+(545920223/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((65995027/125000000 : ℝ)*X 1 0+(-790053071/5000000000 : ℝ)*X 1 1+(682400213/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1055920267/2000000000 : ℝ)*X 2 0+(5459202293/10000000000 : ℝ)*X 2 1+(-1580106463/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2107973801/5000000000 : ℝ)*X 0 0+(4565531801/10000000000 : ℝ)*X 0 1+(777563219/2000000000 : ℝ)*X 0 2+(2107973801/5000000000 : ℝ)*X 1 0+(4565531801/10000000000 : ℝ)*X 1 1+(777563219/2000000000 : ℝ)*X 1 2+(2107973801/5000000000 : ℝ)*X 2 0+(4565531801/10000000000 : ℝ)*X 2 1+(777563219/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8046670351101561460613091/1301875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10183851/1000000000000 : ℝ)*(base19) + (957625221/100000000000000 : ℝ)*(base23) + (36085481/100000000000000 : ℝ)*(lower2) + (77731713/50000000000000 : ℝ)*(upper3) + (106180909/100000000000000 : ℝ)*(upper5) + (3128924727351/125000000000 : ℝ)*(major0) + (3128924727351/125000000000 : ℝ)*(major1) + (3128924727351/125000000000 : ℝ)*(major2) + (1776406910667653/50000000000000 : ℝ)*(sp0) + (1776412487615753/50000000000000 : ℝ)*(sp1) + (710565007198277/20000000000000 : ℝ)*(sp2) + (726723990267979/50000000000000 : ℝ)*(sp3) + (121722813/1000000000000 : ℝ)*(sp4) + (1076716261/20000000000000 : ℝ)*(sp7) + (1453453364117263/100000000000000 : ℝ)*(f.failure) + (1776412996808303/50000000000000 : ℝ)*(f.sum) + (940058496299/260375000000000000000000000 : ℝ)*base66 + (537182426814741/650937500000000000000000000000 : ℝ)*base68 + (902927769722759/650937500000000000000000000000 : ℝ)*base69 + (13865067577501357/1301875000000000000000000000000 : ℝ)*base72 + (1789953052867/416600000000000000000000000 : ℝ)*base73 + (402753059723529/162734375000000000000000000000 : ℝ)*base76 + (3477181243177683/325468750000000000000000000000 : ℝ)*base78 + (1580104907297683/325468750000000000000000000000 : ℝ)*base80 + (11776627360687/2083000000000000000000000000 : ℝ)*base81 + (22641679/2000000000000000000000 : ℝ)*base89 + (22641679/2000000000000000000000 : ℝ)*base91 + (22641679/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (972975790410612370220055141/130187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (321654469/25000000000000 : ℝ)*(base19) + (186461901/25000000000000 : ℝ)*(base23) + (60426549/100000000000000 : ℝ)*(upper3) + (2152647/3125000000000 : ℝ)*(lower4) + (280381861/100000000000000 : ℝ)*(upper5) + (1270590338417271/50000000000000 : ℝ)*(major0) + (1270590338417271/50000000000000 : ℝ)*(major1) + (1270590338417271/50000000000000 : ℝ)*(major2) + (1494914317/12500000000000 : ℝ)*(sp1) + (4351532253/100000000000000 : ℝ)*(sp2) + (450852401874139/12500000000000 : ℝ)*(sp4) + (36068059690607/1000000000000 : ℝ)*(sp5) + (1803407058806627/50000000000000 : ℝ)*(sp6) + (295108377910861/20000000000000 : ℝ)*(sp7) + (295108377910861/20000000000000 : ℝ)*(f.failure) + (450852401874139/12500000000000 : ℝ)*(f.sum) + (3698990623017/5207500000000000000000000000 : ℝ)*base65 + (4220668984374827453/520750000000000000000000000000000 : ℝ)*base67 + (940751046891672547/520750000000000000000000000000000 : ℝ)*base70 + (36594347092077453/520750000000000000000000000000000 : ℝ)*base71 + (38095674589529/10415000000000000000000000000 : ℝ)*base73 + (941099379690327453/520750000000000000000000000000000 : ℝ)*base75 + (3508551138338327453/520750000000000000000000000000000 : ℝ)*base77 + (3137278527503827453/520750000000000000000000000000000 : ℝ)*base79 + (49481538251581/10415000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (657587/400000000000000000000 : ℝ)*base90 + (657587/400000000000000000000 : ℝ)*base92 + (657587/400000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1606_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34444033/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16511/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5131/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2599/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8181/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1606_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1606_s4_0 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-428599981/2500000000 : ℝ)*x 0 + (42661577/78125000 : ℝ)*x 1 + (2590203573/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428599981/2500000000 : ℝ)^4743 ≤ (10549464243657/100000000000000 : ℝ)^3719 := by
    have hnat : (428599981 : ℕ)^4743*100000000000000^3719 ≤ 10549464243657^3719*2500000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428599981 2500000000 10549464243657 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42661577/78125000 : ℝ)^4743 ≤ (23113711547763/50000000000000 : ℝ)^3719 := by
    have hnat : (42661577 : ℕ)^4743*50000000000000^3719 ≤ 23113711547763^3719*78125000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42661577 78125000 23113711547763 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2590203573/5000000000 : ℝ)^4743 ≤ (43223112651351/100000000000000 : ℝ)^3719 := by
    have hnat : (2590203573 : ℕ)^4743*100000000000000^3719 ≤ 43223112651351^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590203573 5000000000 43223112651351 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-428599981/2500000000 : ℝ), (42661577/78125000 : ℝ), (2590203573/5000000000 : ℝ)] ![(10549464243657/100000000000000 : ℝ), (23113711547763/50000000000000 : ℝ), (43223112651351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-428599981/2500000000 : ℝ)|^4743 ≤ (10549464243657/100000000000000 : ℝ)^3719
        have hw : |(-428599981/2500000000 : ℝ)|=(428599981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42661577/78125000 : ℝ)|^4743 ≤ (23113711547763/50000000000000 : ℝ)^3719
        have hw : |(42661577/78125000 : ℝ)|=(42661577/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2590203573/5000000000 : ℝ)|^4743 ≤ (43223112651351/100000000000000 : ℝ)^3719
        have hw : |(2590203573/5000000000 : ℝ)|=(2590203573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s4_1 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669266049/1250000000 : ℝ)*x 0 + (-1858948633/10000000000 : ℝ)*x 1 + (5180407133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669266049/1250000000 : ℝ)^4743 ≤ (45080132254601/100000000000000 : ℝ)^3719 := by
    have hnat : (669266049 : ℕ)^4743*100000000000000^3719 ≤ 45080132254601^3719*1250000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669266049 1250000000 45080132254601 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1858948633/10000000000 : ℝ)^4743 ≤ (11696755219169/100000000000000 : ℝ)^3719 := by
    have hnat : (1858948633 : ℕ)^4743*100000000000000^3719 ≤ 11696755219169^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1858948633 10000000000 11696755219169 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5180407133/10000000000 : ℝ)^4743 ≤ (43223112513019/100000000000000 : ℝ)^3719 := by
    have hnat : (5180407133 : ℕ)^4743*100000000000000^3719 ≤ 43223112513019^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180407133 10000000000 43223112513019 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669266049/1250000000 : ℝ), (-1858948633/10000000000 : ℝ), (5180407133/10000000000 : ℝ)] ![(45080132254601/100000000000000 : ℝ), (11696755219169/100000000000000 : ℝ), (43223112513019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669266049/1250000000 : ℝ)|^4743 ≤ (45080132254601/100000000000000 : ℝ)^3719
        have hw : |(669266049/1250000000 : ℝ)|=(669266049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1858948633/10000000000 : ℝ)|^4743 ≤ (11696755219169/100000000000000 : ℝ)^3719
        have hw : |(-1858948633/10000000000 : ℝ)|=(1858948633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5180407133/10000000000 : ℝ)|^4743 ≤ (43223112513019/100000000000000 : ℝ)^3719
        have hw : |(5180407133/10000000000 : ℝ)|=(5180407133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s4_2 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354128351/10000000000 : ℝ)*x 0 + (1295101799/2500000000 : ℝ)*x 1 + (-464737151/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354128351/10000000000 : ℝ)^4743 ≤ (5635016476793/12500000000000 : ℝ)^3719 := by
    have hnat : (5354128351 : ℕ)^4743*12500000000000^3719 ≤ 5635016476793^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354128351 10000000000 5635016476793 12500000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295101799/2500000000 : ℝ)^4743 ≤ (10805778295849/25000000000000 : ℝ)^3719 := by
    have hnat : (1295101799 : ℕ)^4743*25000000000000^3719 ≤ 10805778295849^3719*2500000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295101799 2500000000 10805778295849 25000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (464737151/2500000000 : ℝ)^4743 ≤ (2339350997291/20000000000000 : ℝ)^3719 := by
    have hnat : (464737151 : ℕ)^4743*20000000000000^3719 ≤ 2339350997291^3719*2500000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464737151 2500000000 2339350997291 20000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354128351/10000000000 : ℝ), (1295101799/2500000000 : ℝ), (-464737151/2500000000 : ℝ)] ![(5635016476793/12500000000000 : ℝ), (10805778295849/25000000000000 : ℝ), (2339350997291/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354128351/10000000000 : ℝ)|^4743 ≤ (5635016476793/12500000000000 : ℝ)^3719
        have hw : |(5354128351/10000000000 : ℝ)|=(5354128351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295101799/2500000000 : ℝ)|^4743 ≤ (10805778295849/25000000000000 : ℝ)^3719
        have hw : |(1295101799/2500000000 : ℝ)|=(1295101799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-464737151/2500000000 : ℝ)|^4743 ≤ (2339350997291/20000000000000 : ℝ)^3719
        have hw : |(-464737151/2500000000 : ℝ)|=(464737151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s4_3 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4215854921/10000000000 : ℝ)*x 0 + (971021473/2500000000 : ℝ)*x 1 + (4569190357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4215854921/10000000000 : ℝ)^4743 ≤ (16617688556317/50000000000000 : ℝ)^3719 := by
    have hnat : (4215854921 : ℕ)^4743*50000000000000^3719 ≤ 16617688556317^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4215854921 10000000000 16617688556317 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (971021473/2500000000 : ℝ)^4743 ≤ (2993659806151/10000000000000 : ℝ)^3719 := by
    have hnat : (971021473 : ℕ)^4743*10000000000000^3719 ≤ 2993659806151^3719*2500000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971021473 2500000000 2993659806151 10000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4569190357/10000000000 : ℝ)^4743 ≤ (36828024809957/100000000000000 : ℝ)^3719 := by
    have hnat : (4569190357 : ℕ)^4743*100000000000000^3719 ≤ 36828024809957^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4569190357 10000000000 36828024809957 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4215854921/10000000000 : ℝ), (971021473/2500000000 : ℝ), (4569190357/10000000000 : ℝ)] ![(16617688556317/50000000000000 : ℝ), (2993659806151/10000000000000 : ℝ), (36828024809957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4215854921/10000000000 : ℝ)|^4743 ≤ (16617688556317/50000000000000 : ℝ)^3719
        have hw : |(4215854921/10000000000 : ℝ)|=(4215854921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(971021473/2500000000 : ℝ)|^4743 ≤ (2993659806151/10000000000000 : ℝ)^3719
        have hw : |(971021473/2500000000 : ℝ)|=(971021473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4569190357/10000000000 : ℝ)|^4743 ≤ (36828024809957/100000000000000 : ℝ)^3719
        have hw : |(4569190357/10000000000 : ℝ)|=(4569190357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s4_4 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-428617707/2500000000 : ℝ)*x 0 + (1295621601/2500000000 : ℝ)*x 1 + (2729290391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428617707/2500000000 : ℝ)^4743 ≤ (5275010341879/50000000000000 : ℝ)^3719 := by
    have hnat : (428617707 : ℕ)^4743*50000000000000^3719 ≤ 5275010341879^3719*2500000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428617707 2500000000 5275010341879 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295621601/2500000000 : ℝ)^4743 ≤ (21622619543711/50000000000000 : ℝ)^3719 := by
    have hnat : (1295621601 : ℕ)^4743*50000000000000^3719 ≤ 21622619543711^3719*2500000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295621601 2500000000 21622619543711 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2729290391/5000000000 : ℝ)^4743 ≤ (23102370110329/50000000000000 : ℝ)^3719 := by
    have hnat : (2729290391 : ℕ)^4743*50000000000000^3719 ≤ 23102370110329^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729290391 5000000000 23102370110329 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-428617707/2500000000 : ℝ), (1295621601/2500000000 : ℝ), (2729290391/5000000000 : ℝ)] ![(5275010341879/50000000000000 : ℝ), (21622619543711/50000000000000 : ℝ), (23102370110329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-428617707/2500000000 : ℝ)|^4743 ≤ (5275010341879/50000000000000 : ℝ)^3719
        have hw : |(-428617707/2500000000 : ℝ)|=(428617707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295621601/2500000000 : ℝ)|^4743 ≤ (21622619543711/50000000000000 : ℝ)^3719
        have hw : |(1295621601/2500000000 : ℝ)|=(1295621601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2729290391/5000000000 : ℝ)|^4743 ≤ (23102370110329/50000000000000 : ℝ)^3719
        have hw : |(2729290391/5000000000 : ℝ)|=(2729290391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s4_5 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055949791/2000000000 : ℝ)*x 0 + (-79038751/500000000 : ℝ)*x 1 + (2729290391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055949791/2000000000 : ℝ)^4743 ≤ (44282978624847/100000000000000 : ℝ)^3719 := by
    have hnat : (1055949791 : ℕ)^4743*100000000000000^3719 ≤ 44282978624847^3719*2000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055949791 2000000000 44282978624847 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (79038751/500000000 : ℝ)^4743 ≤ (9512281137589/100000000000000 : ℝ)^3719 := by
    have hnat : (79038751 : ℕ)^4743*100000000000000^3719 ≤ 9512281137589^3719*500000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79038751 500000000 9512281137589 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2729290391/5000000000 : ℝ)^4743 ≤ (23102370110329/50000000000000 : ℝ)^3719 := by
    have hnat : (2729290391 : ℕ)^4743*50000000000000^3719 ≤ 23102370110329^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729290391 5000000000 23102370110329 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055949791/2000000000 : ℝ), (-79038751/500000000 : ℝ), (2729290391/5000000000 : ℝ)] ![(44282978624847/100000000000000 : ℝ), (9512281137589/100000000000000 : ℝ), (23102370110329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055949791/2000000000 : ℝ)|^4743 ≤ (44282978624847/100000000000000 : ℝ)^3719
        have hw : |(1055949791/2000000000 : ℝ)|=(1055949791/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-79038751/500000000 : ℝ)|^4743 ≤ (9512281137589/100000000000000 : ℝ)^3719
        have hw : |(-79038751/500000000 : ℝ)|=(79038751/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2729290391/5000000000 : ℝ)|^4743 ≤ (23102370110329/50000000000000 : ℝ)^3719
        have hw : |(2729290391/5000000000 : ℝ)|=(2729290391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s4_6 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639874477/5000000000 : ℝ)*x 0 + (2729290391/5000000000 : ℝ)*x 1 + (-1580775021/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639874477/5000000000 : ℝ)^4743 ≤ (885659572283/2000000000000 : ℝ)^3719 := by
    have hnat : (2639874477 : ℕ)^4743*2000000000000^3719 ≤ 885659572283^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639874477 5000000000 885659572283 2000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2729290391/5000000000 : ℝ)^4743 ≤ (23102370110329/50000000000000 : ℝ)^3719 := by
    have hnat : (2729290391 : ℕ)^4743*50000000000000^3719 ≤ 23102370110329^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729290391 5000000000 23102370110329 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1580775021/10000000000 : ℝ)^4743 ≤ (594517571579/6250000000000 : ℝ)^3719 := by
    have hnat : (1580775021 : ℕ)^4743*6250000000000^3719 ≤ 594517571579^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1580775021 10000000000 594517571579 6250000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639874477/5000000000 : ℝ), (2729290391/5000000000 : ℝ), (-1580775021/10000000000 : ℝ)] ![(885659572283/2000000000000 : ℝ), (23102370110329/50000000000000 : ℝ), (594517571579/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639874477/5000000000 : ℝ)|^4743 ≤ (885659572283/2000000000000 : ℝ)^3719
        have hw : |(2639874477/5000000000 : ℝ)|=(2639874477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2729290391/5000000000 : ℝ)|^4743 ≤ (23102370110329/50000000000000 : ℝ)^3719
        have hw : |(2729290391/5000000000 : ℝ)|=(2729290391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1580775021/10000000000 : ℝ)|^4743 ≤ (594517571579/6250000000000 : ℝ)^3719
        have hw : |(-1580775021/10000000000 : ℝ)|=(1580775021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s4_7 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4216028299/10000000000 : ℝ)*x 0 + (1141026959/2500000000 : ℝ)*x 1 + (155568873/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4216028299/10000000000 : ℝ)^4743 ≤ (16618560138517/50000000000000 : ℝ)^3719 := by
    have hnat : (4216028299 : ℕ)^4743*50000000000000^3719 ≤ 16618560138517^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216028299 10000000000 16618560138517 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1141026959/2500000000 : ℝ)^4743 ≤ (36775787744257/100000000000000 : ℝ)^3719 := by
    have hnat : (1141026959 : ℕ)^4743*100000000000000^3719 ≤ 36775787744257^3719*2500000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1141026959 2500000000 36775787744257 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (155568873/400000000 : ℝ)^4743 ≤ (14993545982459/50000000000000 : ℝ)^3719 := by
    have hnat : (155568873 : ℕ)^4743*50000000000000^3719 ≤ 14993545982459^3719*400000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      155568873 400000000 14993545982459 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4216028299/10000000000 : ℝ), (1141026959/2500000000 : ℝ), (155568873/400000000 : ℝ)] ![(16618560138517/50000000000000 : ℝ), (36775787744257/100000000000000 : ℝ), (14993545982459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4216028299/10000000000 : ℝ)|^4743 ≤ (16618560138517/50000000000000 : ℝ)^3719
        have hw : |(4216028299/10000000000 : ℝ)|=(4216028299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1141026959/2500000000 : ℝ)|^4743 ≤ (36775787744257/100000000000000 : ℝ)^3719
        have hw : |(1141026959/2500000000 : ℝ)|=(1141026959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(155568873/400000000 : ℝ)|^4743 ≤ (14993545982459/50000000000000 : ℝ)^3719
        have hw : |(155568873/400000000 : ℝ)|=(155568873/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1606_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34444033/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8181/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2599/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1301/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16349/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8181/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2599/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8181/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2599/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8181/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2599/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8181/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2599/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8181/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2599/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8181/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2599/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2599/25000 : ℝ) ^ (4739/1024 : ℝ) ≤ (2819202215239109/100000000000000000000 : ℝ) := by
    have hpowers : (2599/25000 : ℝ)^4739 ≤ (2819202215239109/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2599 : ℕ)^4739*100000000000000000000^1024 ≤ 2819202215239109^1024*25000^4739 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2599 25000 2819202215239109 100000000000000000000 4739 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2599/25000 : ℝ)) (X := (2819202215239109/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8181/50000 : ℝ) ^ (4739/1024 : ℝ) ≤ (22998000670425167/100000000000000000000 : ℝ) := by
    have hpowers : (8181/50000 : ℝ)^4739 ≤ (22998000670425167/100000000000000000000 : ℝ)^1024 := by
      have hnat : (8181 : ℕ)^4739*100000000000000000000^1024 ≤ 22998000670425167^1024*50000^4739 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8181 50000 22998000670425167 100000000000000000000 4739 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8181/50000 : ℝ)) (X := (22998000670425167/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002819202215239109/50000000000000000000 : ℝ) ≤ (2500030457894809/2500000000000000 : ℝ) ^ (4739/1024 : ℝ) := by
    have hpowers : (50002819202215239109/50000000000000000000 : ℝ)^1024 ≤ (2500030457894809/2500000000000000 : ℝ)^4739 := by
      have hnat : (50002819202215239109 : ℕ)^1024*2500000000000000^4739 ≤ 2500030457894809^4739*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002819202215239109 50000000000000000000 2500030457894809 2500000000000000 1024 4739 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500030457894809/2500000000000000 : ℝ)) (X := (50002819202215239109/50000000000000000000 : ℝ)) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25006454300721416069/25000000000000000000 : ℝ) ≤ (10000557799977627/10000000000000000 : ℝ) ^ (4739/1024 : ℝ) := by
    have hpowers : (25006454300721416069/25000000000000000000 : ℝ)^1024 ≤ (10000557799977627/10000000000000000 : ℝ)^4739 := by
      have hnat : (25006454300721416069 : ℕ)^1024*10000000000000000^4739 ≤ 10000557799977627^4739*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006454300721416069 25000000000000000000 10000557799977627 10000000000000000 1024 4739 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000557799977627/10000000000000000 : ℝ)) (X := (25006454300721416069/25000000000000000000 : ℝ)) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50022998000670425167/50000000000000000000 : ℝ) ≤ (5000496884188009/5000000000000000 : ℝ) ^ (4739/1024 : ℝ) := by
    have hpowers : (50022998000670425167/50000000000000000000 : ℝ)^1024 ≤ (5000496884188009/5000000000000000 : ℝ)^4739 := by
      have hnat : (50022998000670425167 : ℕ)^1024*5000000000000000^4739 ≤ 5000496884188009^4739*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022998000670425167 50000000000000000000 5000496884188009 5000000000000000 1024 4739 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000496884188009/5000000000000000 : ℝ)) (X := (50022998000670425167/50000000000000000000 : ℝ)) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2819202215239109/100000000000000000000 : ℝ) ≤ ((3728228887016398519/3728750000000000000 : ℝ)+2*(435968398391/596600000000000 : ℝ)*(2599/25000 : ℝ))^(4739/1024 : ℝ) := by
    rw [show (3728228887016398519/3728750000000000000 : ℝ)+2*(435968398391/596600000000000 : ℝ)*(2599/25000 : ℝ)=(2500030457894809/2500000000000000 : ℝ) by norm_num, show 1+2*(2819202215239109/100000000000000000000 : ℝ)=(50002819202215239109/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22998000670425167/100000000000000000000 : ℝ)+(2819202215239109/100000000000000000000 : ℝ) ≤ ((3728228887016398519/3728750000000000000 : ℝ)+(435968398391/596600000000000 : ℝ)*((8181/50000 : ℝ)+(2599/25000 : ℝ)))^(4739/1024 : ℝ) := by
    rw [show (3728228887016398519/3728750000000000000 : ℝ)+(435968398391/596600000000000 : ℝ)*((8181/50000 : ℝ)+(2599/25000 : ℝ))=(10000557799977627/10000000000000000 : ℝ) by norm_num, show 1+(22998000670425167/100000000000000000000 : ℝ)+(2819202215239109/100000000000000000000 : ℝ)=(25006454300721416069/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22998000670425167/100000000000000000000 : ℝ) ≤ ((3728228887016398519/3728750000000000000 : ℝ)+2*(435968398391/596600000000000 : ℝ)*(8181/50000 : ℝ))^(4739/1024 : ℝ) := by
    rw [show (3728228887016398519/3728750000000000000 : ℝ)+2*(435968398391/596600000000000 : ℝ)*(8181/50000 : ℝ)=(5000496884188009/5000000000000000 : ℝ) by norm_num, show 1+2*(22998000670425167/100000000000000000000 : ℝ)=(50022998000670425167/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3728228887016398519/3728750000000000000 : ℝ)*(X 1 0+X 2 0)+(435968398391/596600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4739/1024 : ℝ)) (lo := (2599/25000 : ℝ)) (hi := (8181/50000 : ℝ)) (c := (3728228887016398519/3728750000000000000 : ℝ)) (alpha := (435968398391/596600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3728228887016398519/3728750000000000000 : ℝ)*(X 0 1+X 2 1)+(435968398391/596600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4739/1024 : ℝ)) (lo := (2599/25000 : ℝ)) (hi := (8181/50000 : ℝ)) (c := (3728228887016398519/3728750000000000000 : ℝ)) (alpha := (435968398391/596600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3728228887016398519/3728750000000000000 : ℝ)*(X 0 2+X 1 2)+(435968398391/596600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4739/1024 : ℝ)) (lo := (2599/25000 : ℝ)) (hi := (8181/50000 : ℝ)) (c := (3728228887016398519/3728750000000000000 : ℝ)) (alpha := (435968398391/596600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-428599981/2500000000 : ℝ)*X 0 0+(42661577/78125000 : ℝ)*X 0 1+(2590203573/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669266049/1250000000 : ℝ)*X 1 0+(-1858948633/10000000000 : ℝ)*X 1 1+(5180407133/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354128351/10000000000 : ℝ)*X 2 0+(1295101799/2500000000 : ℝ)*X 2 1+(-464737151/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4215854921/10000000000 : ℝ)*X 0 0+(971021473/2500000000 : ℝ)*X 0 1+(4569190357/10000000000 : ℝ)*X 0 2+(4215854921/10000000000 : ℝ)*X 1 0+(971021473/2500000000 : ℝ)*X 1 1+(4569190357/10000000000 : ℝ)*X 1 2+(4215854921/10000000000 : ℝ)*X 2 0+(971021473/2500000000 : ℝ)*X 2 1+(4569190357/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-428617707/2500000000 : ℝ)*X 0 0+(1295621601/2500000000 : ℝ)*X 0 1+(2729290391/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1055949791/2000000000 : ℝ)*X 1 0+(-79038751/500000000 : ℝ)*X 1 1+(2729290391/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2639874477/5000000000 : ℝ)*X 2 0+(2729290391/5000000000 : ℝ)*X 2 1+(-1580775021/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4216028299/10000000000 : ℝ)*X 0 0+(1141026959/2500000000 : ℝ)*X 0 1+(155568873/400000000 : ℝ)*X 0 2+(4216028299/10000000000 : ℝ)*X 1 0+(1141026959/2500000000 : ℝ)*X 1 1+(155568873/400000000 : ℝ)*X 1 2+(4216028299/10000000000 : ℝ)*X 2 0+(1141026959/2500000000 : ℝ)*X 2 1+(155568873/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (124463372683478780905116219/23304687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (94787333/10000000000000 : ℝ)*(base19) + (439688329/50000000000000 : ℝ)*(base23) + (110227/500000000000 : ℝ)*(lower2) + (62881393/50000000000000 : ℝ)*(upper3) + (22610937/20000000000000 : ℝ)*(upper5) + (2513796367553307/100000000000000 : ℝ)*(major0) + (2513796367553307/100000000000000 : ℝ)*(major1) + (2513796367553307/100000000000000 : ℝ)*(major2) + (3567939689200491/100000000000000 : ℝ)*(sp0) + (3567950476272131/100000000000000 : ℝ)*(sp1) + (1783975272384401/50000000000000 : ℝ)*(sp2) + (364909040451271/25000000000000 : ℝ)*(sp3) + (1173494497/10000000000000 : ℝ)*(sp4) + (1242783173/25000000000000 : ℝ)*(sp7) + (91227570808611/6250000000000 : ℝ)*(f.failure) + (178397571207273/5000000000000 : ℝ)*(f.sum) + (105400553831797/29830000000000000000000000000 : ℝ)*base65 + (1068240197746166417/372875000000000000000000000000000 : ℝ)*base68 + (990691842562083583/372875000000000000000000000000000 : ℝ)*base69 + (324640327770833583/372875000000000000000000000000000 : ℝ)*base71 + (13144793553073/29830000000000000000000000000 : ℝ)*base74 + (614522418480708583/372875000000000000000000000000000 : ℝ)*base75 + (838066028589583583/372875000000000000000000000000000 : ℝ)*base77 + (1551609376287833583/372875000000000000000000000000000 : ℝ)*base79 + (114219672460637/29830000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (218163/125000000000000000000 : ℝ)*base89 + (218163/125000000000000000000 : ℝ)*base91 + (218163/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3119646723127968432055713/296875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (202319079/12500000000000 : ℝ)*(base19) + (54744251/3125000000000 : ℝ)*(base23) + (64280817/12500000000000 : ℝ)*(lower1) + (220806067/100000000000000 : ℝ)*(upper3) + (60342203/100000000000000 : ℝ)*(lower4) + (8703701/4000000000000 : ℝ)*(upper5) + (637956821197629/25000000000000 : ℝ)*(major0) + (637956821197629/25000000000000 : ℝ)*(major1) + (637956821197629/25000000000000 : ℝ)*(major2) + (174438777/12500000000000 : ℝ)*(sp2) + (905482588628029/25000000000000 : ℝ)*(sp4) + (905482183989871/25000000000000 : ℝ)*(sp5) + (905481801796467/25000000000000 : ℝ)*(sp6) + (370430966198197/25000000000000 : ℝ)*(sp7) + (370430966198197/25000000000000 : ℝ)*(f.failure) + (905482588628029/25000000000000 : ℝ)*(f.sum) + (51664054163/47500000000000000000000000 : ℝ)*base66 + (5971113672020893/593750000000000000000000000000 : ℝ)*base67 + (2536391533895893/593750000000000000000000000000 : ℝ)*base69 + (7900154459520893/593750000000000000000000000000 : ℝ)*base71 + (78331973447/47500000000000000000000000 : ℝ)*base73 + (3540255479395893/593750000000000000000000000000 : ℝ)*base75 + (252074562895893/593750000000000000000000000000 : ℝ)*base77 + (2882763274770893/593750000000000000000000000000 : ℝ)*base79 + (65751155747/47500000000000000000000000 : ℝ)*base81 + (2008501/500000000000000000000 : ℝ)*base89 + (2008501/500000000000000000000 : ℝ)*base91 + (2008501/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1606_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34444033/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8181/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2599/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1301/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16349/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1606_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1606_s5_0 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-857204443/5000000000 : ℝ)*x 0 + (5460627179/10000000000 : ℝ)*x 1 + (1295114003/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (857204443/5000000000 : ℝ)^4743 ≤ (10549534575251/100000000000000 : ℝ)^3719 := by
    have hnat : (857204443 : ℕ)^4743*100000000000000^3719 ≤ 10549534575251^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857204443 5000000000 10549534575251 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5460627179/10000000000 : ℝ)^4743 ≤ (5778354097563/12500000000000 : ℝ)^3719 := by
    have hnat : (5460627179 : ℕ)^4743*12500000000000^3719 ≤ 5778354097563^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5460627179 10000000000 5778354097563 12500000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295114003/2500000000 : ℝ)^4743 ≤ (43223632631119/100000000000000 : ℝ)^3719 := by
    have hnat : (1295114003 : ℕ)^4743*100000000000000^3719 ≤ 43223632631119^3719*2500000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295114003 2500000000 43223632631119 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-857204443/5000000000 : ℝ), (5460627179/10000000000 : ℝ), (1295114003/2500000000 : ℝ)] ![(10549534575251/100000000000000 : ℝ), (5778354097563/12500000000000 : ℝ), (43223632631119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-857204443/5000000000 : ℝ)|^4743 ≤ (10549534575251/100000000000000 : ℝ)^3719
        have hw : |(-857204443/5000000000 : ℝ)|=(857204443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5460627179/10000000000 : ℝ)|^4743 ≤ (5778354097563/12500000000000 : ℝ)^3719
        have hw : |(5460627179/10000000000 : ℝ)|=(5460627179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295114003/2500000000 : ℝ)|^4743 ≤ (43223632631119/100000000000000 : ℝ)^3719
        have hw : |(1295114003/2500000000 : ℝ)|=(1295114003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s5_1 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338528253/2500000000 : ℝ)*x 0 + (-23236309/125000000 : ℝ)*x 1 + (518045577/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338528253/2500000000 : ℝ)^4743 ≤ (45079967104247/100000000000000 : ℝ)^3719 := by
    have hnat : (1338528253 : ℕ)^4743*100000000000000^3719 ≤ 45079967104247^3719*2500000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338528253 2500000000 45079967104247 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (23236309/125000000 : ℝ)^4743 ≤ (5848201417393/50000000000000 : ℝ)^3719 := by
    have hnat : (23236309 : ℕ)^4743*50000000000000^3719 ≤ 5848201417393^3719*125000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23236309 125000000 5848201417393 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518045577/1000000000 : ℝ)^4743 ≤ (4322363005601/10000000000000 : ℝ)^3719 := by
    have hnat : (518045577 : ℕ)^4743*10000000000000^3719 ≤ 4322363005601^3719*1000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518045577 1000000000 4322363005601 10000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338528253/2500000000 : ℝ), (-23236309/125000000 : ℝ), (518045577/1000000000 : ℝ)] ![(45079967104247/100000000000000 : ℝ), (5848201417393/50000000000000 : ℝ), (4322363005601/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338528253/2500000000 : ℝ)|^4743 ≤ (45079967104247/100000000000000 : ℝ)^3719
        have hw : |(1338528253/2500000000 : ℝ)|=(1338528253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-23236309/125000000 : ℝ)|^4743 ≤ (5848201417393/50000000000000 : ℝ)^3719
        have hw : |(-23236309/125000000 : ℝ)|=(23236309/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518045577/1000000000 : ℝ)|^4743 ≤ (4322363005601/10000000000000 : ℝ)^3719
        have hw : |(518045577/1000000000 : ℝ)|=(518045577/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s5_2 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669264367/1250000000 : ℝ)*x 0 + (5180454361/10000000000 : ℝ)*x 1 + (-929452007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669264367/1250000000 : ℝ)^4743 ≤ (45079987764141/100000000000000 : ℝ)^3719 := by
    have hnat : (669264367 : ℕ)^4743*100000000000000^3719 ≤ 45079987764141^3719*1250000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669264367 1250000000 45079987764141 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5180454361/10000000000 : ℝ)^4743 ≤ (21611807531459/50000000000000 : ℝ)^3719 := by
    have hnat : (5180454361 : ℕ)^4743*50000000000000^3719 ≤ 21611807531459^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180454361 10000000000 21611807531459 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (929452007/5000000000 : ℝ)^4743 ≤ (2339279433887/20000000000000 : ℝ)^3719 := by
    have hnat : (929452007 : ℕ)^4743*20000000000000^3719 ≤ 2339279433887^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929452007 5000000000 2339279433887 20000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669264367/1250000000 : ℝ), (5180454361/10000000000 : ℝ), (-929452007/5000000000 : ℝ)] ![(45079987764141/100000000000000 : ℝ), (21611807531459/50000000000000 : ℝ), (2339279433887/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669264367/1250000000 : ℝ)|^4743 ≤ (45079987764141/100000000000000 : ℝ)^3719
        have hw : |(669264367/1250000000 : ℝ)|=(669264367/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5180454361/10000000000 : ℝ)|^4743 ≤ (21611807531459/50000000000000 : ℝ)^3719
        have hw : |(5180454361/10000000000 : ℝ)|=(5180454361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-929452007/5000000000 : ℝ)|^4743 ≤ (2339279433887/20000000000000 : ℝ)^3719
        have hw : |(-929452007/5000000000 : ℝ)|=(929452007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s5_3 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1053965741/2500000000 : ℝ)*x 0 + (1942104537/5000000000 : ℝ)*x 1 + (571133087/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053965741/2500000000 : ℝ)^4743 ≤ (1661772898877/5000000000000 : ℝ)^3719 := by
    have hnat : (1053965741 : ℕ)^4743*5000000000000^3719 ≤ 1661772898877^3719*2500000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053965741 2500000000 1661772898877 5000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1942104537/5000000000 : ℝ)^4743 ≤ (119751235639/400000000000 : ℝ)^3719 := by
    have hnat : (1942104537 : ℕ)^4743*400000000000^3719 ≤ 119751235639^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1942104537 5000000000 119751235639 400000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (571133087/1250000000 : ℝ)^4743 ≤ (7365346620011/20000000000000 : ℝ)^3719 := by
    have hnat : (571133087 : ℕ)^4743*20000000000000^3719 ≤ 7365346620011^3719*1250000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571133087 1250000000 7365346620011 20000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053965741/2500000000 : ℝ), (1942104537/5000000000 : ℝ), (571133087/1250000000 : ℝ)] ![(1661772898877/5000000000000 : ℝ), (119751235639/400000000000 : ℝ), (7365346620011/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053965741/2500000000 : ℝ)|^4743 ≤ (1661772898877/5000000000000 : ℝ)^3719
        have hw : |(1053965741/2500000000 : ℝ)|=(1053965741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1942104537/5000000000 : ℝ)|^4743 ≤ (119751235639/400000000000 : ℝ)^3719
        have hw : |(1942104537/5000000000 : ℝ)|=(1942104537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(571133087/1250000000 : ℝ)|^4743 ≤ (7365346620011/20000000000000 : ℝ)^3719
        have hw : |(571133087/1250000000 : ℝ)|=(571133087/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s5_4 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1714481369/10000000000 : ℝ)*x 0 + (2591266341/5000000000 : ℝ)*x 1 + (2729263749/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1714481369/10000000000 : ℝ)^4743 ≤ (10550103407913/100000000000000 : ℝ)^3719 := by
    have hnat : (1714481369 : ℕ)^4743*100000000000000^3719 ≤ 10550103407913^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1714481369 10000000000 10550103407913 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591266341/5000000000 : ℝ)^4743 ≤ (21622865791419/50000000000000 : ℝ)^3719 := by
    have hnat : (2591266341 : ℕ)^4743*50000000000000^3719 ≤ 21622865791419^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591266341 5000000000 21622865791419 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2729263749/5000000000 : ℝ)^4743 ≤ (23102082502981/50000000000000 : ℝ)^3719 := by
    have hnat : (2729263749 : ℕ)^4743*50000000000000^3719 ≤ 23102082502981^3719*5000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729263749 5000000000 23102082502981 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1714481369/10000000000 : ℝ), (2591266341/5000000000 : ℝ), (2729263749/5000000000 : ℝ)] ![(10550103407913/100000000000000 : ℝ), (21622865791419/50000000000000 : ℝ), (23102082502981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1714481369/10000000000 : ℝ)|^4743 ≤ (10550103407913/100000000000000 : ℝ)^3719
        have hw : |(-1714481369/10000000000 : ℝ)|=(1714481369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591266341/5000000000 : ℝ)|^4743 ≤ (21622865791419/50000000000000 : ℝ)^3719
        have hw : |(2591266341/5000000000 : ℝ)|=(2591266341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2729263749/5000000000 : ℝ)|^4743 ≤ (23102082502981/50000000000000 : ℝ)^3719
        have hw : |(2729263749/5000000000 : ℝ)|=(2729263749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s5_5 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1319940403/2500000000 : ℝ)*x 0 + (-49401003/312500000 : ℝ)*x 1 + (1091705533/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319940403/2500000000 : ℝ)^4743 ≤ (11070778503309/25000000000000 : ℝ)^3719 := by
    have hnat : (1319940403 : ℕ)^4743*25000000000000^3719 ≤ 11070778503309^3719*2500000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319940403 2500000000 11070778503309 25000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49401003/312500000 : ℝ)^4743 ≤ (2378179790231/25000000000000 : ℝ)^3719 := by
    have hnat : (49401003 : ℕ)^4743*25000000000000^3719 ≤ 2378179790231^3719*312500000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49401003 312500000 2378179790231 25000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091705533/2000000000 : ℝ)^4743 ≤ (46204166808769/100000000000000 : ℝ)^3719 := by
    have hnat : (1091705533 : ℕ)^4743*100000000000000^3719 ≤ 46204166808769^3719*2000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091705533 2000000000 46204166808769 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319940403/2500000000 : ℝ), (-49401003/312500000 : ℝ), (1091705533/2000000000 : ℝ)] ![(11070778503309/25000000000000 : ℝ), (2378179790231/25000000000000 : ℝ), (46204166808769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319940403/2500000000 : ℝ)|^4743 ≤ (11070778503309/25000000000000 : ℝ)^3719
        have hw : |(1319940403/2500000000 : ℝ)|=(1319940403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-49401003/312500000 : ℝ)|^4743 ≤ (2378179790231/25000000000000 : ℝ)^3719
        have hw : |(-49401003/312500000 : ℝ)|=(49401003/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1091705533/2000000000 : ℝ)|^4743 ≤ (46204166808769/100000000000000 : ℝ)^3719
        have hw : |(1091705533/2000000000 : ℝ)|=(1091705533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s5_6 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5279761717/10000000000 : ℝ)*x 0 + (5458527579/10000000000 : ℝ)*x 1 + (-197604009/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5279761717/10000000000 : ℝ)^4743 ≤ (5535389392049/12500000000000 : ℝ)^3719 := by
    have hnat : (5279761717 : ℕ)^4743*12500000000000^3719 ≤ 5535389392049^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5279761717 10000000000 5535389392049 12500000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5458527579/10000000000 : ℝ)^4743 ≤ (46204165880377/100000000000000 : ℝ)^3719 := by
    have hnat : (5458527579 : ℕ)^4743*100000000000000^3719 ≤ 46204165880377^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458527579 10000000000 46204165880377 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (197604009/1250000000 : ℝ)^4743 ≤ (4756359488369/50000000000000 : ℝ)^3719 := by
    have hnat : (197604009 : ℕ)^4743*50000000000000^3719 ≤ 4756359488369^3719*1250000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197604009 1250000000 4756359488369 50000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5279761717/10000000000 : ℝ), (5458527579/10000000000 : ℝ), (-197604009/1250000000 : ℝ)] ![(5535389392049/12500000000000 : ℝ), (46204165880377/100000000000000 : ℝ), (4756359488369/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5279761717/10000000000 : ℝ)|^4743 ≤ (5535389392049/12500000000000 : ℝ)^3719
        have hw : |(5279761717/10000000000 : ℝ)|=(5279761717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5458527579/10000000000 : ℝ)|^4743 ≤ (46204165880377/100000000000000 : ℝ)^3719
        have hw : |(5458527579/10000000000 : ℝ)|=(5458527579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-197604009/1250000000 : ℝ)|^4743 ≤ (4756359488369/50000000000000 : ℝ)^3719
        have hw : |(-197604009/1250000000 : ℝ)|=(197604009/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1606_s5_7 (p : ℝ) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4216035157/10000000000 : ℝ)*x 0 + (57049819/125000000 : ℝ)*x 1 + (3889342637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4216035157/10000000000 : ℝ)^4743 ≤ (33237189228641/100000000000000 : ℝ)^3719 := by
    have hnat : (4216035157 : ℕ)^4743*100000000000000^3719 ≤ 33237189228641^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216035157 10000000000 33237189228641 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (57049819/125000000 : ℝ)^4743 ≤ (36774530803811/100000000000000 : ℝ)^3719 := by
    have hnat : (57049819 : ℕ)^4743*100000000000000^3719 ≤ 36774530803811^3719*125000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57049819 125000000 36774530803811 100000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3889342637/10000000000 : ℝ)^4743 ≤ (7497069987177/25000000000000 : ℝ)^3719 := by
    have hnat : (3889342637 : ℕ)^4743*25000000000000^3719 ≤ 7497069987177^3719*10000000000^4743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3889342637 10000000000 7497069987177 25000000000000 4743 3719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4743/1024 : ℝ)) 4743 3719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4216035157/10000000000 : ℝ), (57049819/125000000 : ℝ), (3889342637/10000000000 : ℝ)] ![(33237189228641/100000000000000 : ℝ), (36774530803811/100000000000000 : ℝ), (7497069987177/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4216035157/10000000000 : ℝ)|^4743 ≤ (33237189228641/100000000000000 : ℝ)^3719
        have hw : |(4216035157/10000000000 : ℝ)|=(4216035157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(57049819/125000000 : ℝ)|^4743 ≤ (36774530803811/100000000000000 : ℝ)^3719
        have hw : |(57049819/125000000 : ℝ)|=(57049819/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3889342637/10000000000 : ℝ)|^4743 ≤ (7497069987177/25000000000000 : ℝ)^3719
        have hw : |(3889342637/10000000000 : ℝ)|=(3889342637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1606_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34444033/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16349/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1301/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (10409/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4087/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16349/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1301/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16349/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1301/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16349/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1301/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16349/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1301/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16349/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1301/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16349/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1301/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1301/12500 : ℝ) ^ (4739/1024 : ℝ) ≤ (1417146942033219/50000000000000000000 : ℝ) := by
    have hpowers : (1301/12500 : ℝ)^4739 ≤ (1417146942033219/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1301 : ℕ)^4739*50000000000000000000^1024 ≤ 1417146942033219^1024*12500^4739 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1301 12500 1417146942033219 50000000000000000000 4739 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1301/12500 : ℝ)) (X := (1417146942033219/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16349/100000 : ℝ) ^ (4739/1024 : ℝ) ≤ (5728389699196829/25000000000000000000 : ℝ) := by
    have hpowers : (16349/100000 : ℝ)^4739 ≤ (5728389699196829/25000000000000000000 : ℝ)^1024 := by
      have hnat : (16349 : ℕ)^4739*25000000000000000000^1024 ≤ 5728389699196829^1024*100000^4739 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16349 100000 5728389699196829 25000000000000000000 4739 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16349/100000 : ℝ)) (X := (5728389699196829/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001417146942033219/25000000000000000000 : ℝ) ≤ (2000024496749981/2000000000000000 : ℝ) ^ (4739/1024 : ℝ) := by
    have hpowers : (25001417146942033219/25000000000000000000 : ℝ)^1024 ≤ (2000024496749981/2000000000000000 : ℝ)^4739 := by
      have hnat : (25001417146942033219 : ℕ)^1024*2000000000000000^4739 ≤ 2000024496749981^4739*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001417146942033219 25000000000000000000 2000024496749981 2000000000000000 1024 4739 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000024496749981/2000000000000000 : ℝ)) (X := (25001417146942033219/25000000000000000000 : ℝ)) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50012873926340426877/50000000000000000000 : ℝ) ≤ (1000055630176577/1000000000000000 : ℝ) ^ (4739/1024 : ℝ) := by
    have hpowers : (50012873926340426877/50000000000000000000 : ℝ)^1024 ≤ (1000055630176577/1000000000000000 : ℝ)^4739 := by
      have hnat : (50012873926340426877 : ℕ)^1024*1000000000000000^4739 ≤ 1000055630176577^4739*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012873926340426877 50000000000000000000 1000055630176577 1000000000000000 1024 4739 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000055630176577/1000000000000000 : ℝ)) (X := (50012873926340426877/50000000000000000000 : ℝ)) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505728389699196829/12500000000000000000 : ℝ) ≤ (2000198023956327/2000000000000000 : ℝ) ^ (4739/1024 : ℝ) := by
    have hpowers : (12505728389699196829/12500000000000000000 : ℝ)^1024 ≤ (2000198023956327/2000000000000000 : ℝ)^4739 := by
      have hnat : (12505728389699196829 : ℕ)^1024*2000000000000000^4739 ≤ 2000198023956327^4739*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505728389699196829 12500000000000000000 2000198023956327 2000000000000000 1024 4739 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000198023956327/2000000000000000 : ℝ)) (X := (12505728389699196829/12500000000000000000 : ℝ)) (by norm_num) 4739 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1417146942033219/50000000000000000000 : ℝ) ≤ ((913872266463691381/914000000000000000 : ℝ)+2*(6674123321/9140000000000 : ℝ)*(1301/12500 : ℝ))^(4739/1024 : ℝ) := by
    rw [show (913872266463691381/914000000000000000 : ℝ)+2*(6674123321/9140000000000 : ℝ)*(1301/12500 : ℝ)=(2000024496749981/2000000000000000 : ℝ) by norm_num, show 1+2*(1417146942033219/50000000000000000000 : ℝ)=(25001417146942033219/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5728389699196829/25000000000000000000 : ℝ)+(1417146942033219/50000000000000000000 : ℝ) ≤ ((913872266463691381/914000000000000000 : ℝ)+(6674123321/9140000000000 : ℝ)*((16349/100000 : ℝ)+(1301/12500 : ℝ)))^(4739/1024 : ℝ) := by
    rw [show (913872266463691381/914000000000000000 : ℝ)+(6674123321/9140000000000 : ℝ)*((16349/100000 : ℝ)+(1301/12500 : ℝ))=(1000055630176577/1000000000000000 : ℝ) by norm_num, show 1+(5728389699196829/25000000000000000000 : ℝ)+(1417146942033219/50000000000000000000 : ℝ)=(50012873926340426877/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5728389699196829/25000000000000000000 : ℝ) ≤ ((913872266463691381/914000000000000000 : ℝ)+2*(6674123321/9140000000000 : ℝ)*(16349/100000 : ℝ))^(4739/1024 : ℝ) := by
    rw [show (913872266463691381/914000000000000000 : ℝ)+2*(6674123321/9140000000000 : ℝ)*(16349/100000 : ℝ)=(2000198023956327/2000000000000000 : ℝ) by norm_num, show 1+2*(5728389699196829/25000000000000000000 : ℝ)=(12505728389699196829/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (913872266463691381/914000000000000000 : ℝ)*(X 1 0+X 2 0)+(6674123321/9140000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4739/1024 : ℝ)) (lo := (1301/12500 : ℝ)) (hi := (16349/100000 : ℝ)) (c := (913872266463691381/914000000000000000 : ℝ)) (alpha := (6674123321/9140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (913872266463691381/914000000000000000 : ℝ)*(X 0 1+X 2 1)+(6674123321/9140000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4739/1024 : ℝ)) (lo := (1301/12500 : ℝ)) (hi := (16349/100000 : ℝ)) (c := (913872266463691381/914000000000000000 : ℝ)) (alpha := (6674123321/9140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (913872266463691381/914000000000000000 : ℝ)*(X 0 2+X 1 2)+(6674123321/9140000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4739/1024 : ℝ)) (lo := (1301/12500 : ℝ)) (hi := (16349/100000 : ℝ)) (c := (913872266463691381/914000000000000000 : ℝ)) (alpha := (6674123321/9140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-857204443/5000000000 : ℝ)*X 0 0+(5460627179/10000000000 : ℝ)*X 0 1+(1295114003/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338528253/2500000000 : ℝ)*X 1 0+(-23236309/125000000 : ℝ)*X 1 1+(518045577/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669264367/1250000000 : ℝ)*X 2 0+(5180454361/10000000000 : ℝ)*X 2 1+(-929452007/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1053965741/2500000000 : ℝ)*X 0 0+(1942104537/5000000000 : ℝ)*X 0 1+(571133087/1250000000 : ℝ)*X 0 2+(1053965741/2500000000 : ℝ)*X 1 0+(1942104537/5000000000 : ℝ)*X 1 1+(571133087/1250000000 : ℝ)*X 1 2+(1053965741/2500000000 : ℝ)*X 2 0+(1942104537/5000000000 : ℝ)*X 2 1+(571133087/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1714481369/10000000000 : ℝ)*X 0 0+(2591266341/5000000000 : ℝ)*X 0 1+(2729263749/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1319940403/2500000000 : ℝ)*X 1 0+(-49401003/312500000 : ℝ)*X 1 1+(1091705533/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5279761717/10000000000 : ℝ)*X 2 0+(5458527579/10000000000 : ℝ)*X 2 1+(-197604009/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4216035157/10000000000 : ℝ)*X 0 0+(57049819/125000000 : ℝ)*X 0 1+(3889342637/10000000000 : ℝ)*X 0 2+(4216035157/10000000000 : ℝ)*X 1 0+(57049819/125000000 : ℝ)*X 1 1+(3889342637/10000000000 : ℝ)*X 1 2+(4216035157/10000000000 : ℝ)*X 2 0+(57049819/125000000 : ℝ)*X 2 1+(3889342637/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1606_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20103488955421774293699093/2856250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (428444627/100000000000000 : ℝ)*(base19) + (277533669/50000000000000 : ℝ)*(base23) + (341248759/50000000000000 : ℝ)*(lower2) + (31785201/50000000000000 : ℝ)*(lower4) + (4551099/4000000000000 : ℝ)*(lower5) + (314338343724651/12500000000000 : ℝ)*(major0) + (314338343724651/12500000000000 : ℝ)*(major1) + (314338343724651/12500000000000 : ℝ)*(major2) + (3569239197107443/100000000000000 : ℝ)*(sp0) + (446155386029843/12500000000000 : ℝ)*(sp1) + (111538842550501/3125000000000 : ℝ)*(sp2) + (730081433822779/50000000000000 : ℝ)*(sp3) + (4319575927/100000000000000 : ℝ)*(sp4) + (344032573/5000000000000 : ℝ)*(sp7) + (730084874148509/50000000000000 : ℝ)*(f.failure) + (356924351668337/10000000000000 : ℝ)*(f.sum) + (1616158723179/457000000000000000000000000 : ℝ)*base66 + (46418967931241969/11425000000000000000000000000000 : ℝ)*base68 + (481041554283031/11425000000000000000000000000000 : ℝ)*base69 + (188774902732466969/11425000000000000000000000000000 : ℝ)*base72 + (96211914171/114250000000000000000000000 : ℝ)*base73 + (81375826383866969/11425000000000000000000000000000 : ℝ)*base76 + (54134899731666969/11425000000000000000000000000000 : ℝ)*base78 + (81779069199666969/11425000000000000000000000000000 : ℝ)*base80 + (167018615203/114250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (10896797/1000000000000000000000 : ℝ)*base89 + (10896797/1000000000000000000000 : ℝ)*base91 + (10896797/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2778182291070361412787/228500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1802558673/100000000000000 : ℝ)*(base19) + (7790109/390625000000 : ℝ)*(base23) + (607351049/100000000000000 : ℝ)*(lower1) + (135891991/50000000000000 : ℝ)*(upper3) + (4705983/10000000000000 : ℝ)*(lower4) + (47059341/20000000000000 : ℝ)*(upper5) + (1276372652685181/50000000000000 : ℝ)*(major0) + (1276372652685181/50000000000000 : ℝ)*(major1) + (1276372652685181/50000000000000 : ℝ)*(major2) + (1083621569/50000000000000 : ℝ)*(sp2) + (452904161261833/12500000000000 : ℝ)*(sp4) + (362323148753599/10000000000000 : ℝ)*(sp5) + (1811614564291811/50000000000000 : ℝ)*(sp6) + (185282114420977/12500000000000 : ℝ)*(sp7) + (185282114420977/12500000000000 : ℝ)*(f.failure) + (452904161261833/12500000000000 : ℝ)*(f.sum) + (126120597567/45700000000000000000000000 : ℝ)*base66 + (201955175768624961/45700000000000000000000000000000 : ℝ)*base67 + (312302733358575039/45700000000000000000000000000000 : ℝ)*base70 + (2234147810811824961/45700000000000000000000000000000 : ℝ)*base71 + (306794994379/228500000000000000000000000 : ℝ)*base74 + (161556331256824961/45700000000000000000000000000000 : ℝ)*base75 + (348253725561575039/45700000000000000000000000000000 : ℝ)*base78 + (275167773066975039/45700000000000000000000000000000 : ℝ)*base80 + (102164704747/45700000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (2680241/250000000000000000000 : ℝ)*base89 + (2680241/250000000000000000000 : ℝ)*base91 + (2680241/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1606_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34444033/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16349/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1301/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10409/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4087/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1606_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1606_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34444033/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16511/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5131/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10409/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4087/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1606_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1606_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1606_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4739/1024 : ℝ) ≤ p) (hpb : p ≤ (4743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (34444033/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16511/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5131/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10409/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4087/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1606_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
