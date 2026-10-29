-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1742_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:13:40.87929+00:00
-- url     : https://prove2.me/submissions/55738645-1051-4af1-8e74-3c0975a04f2e

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
theorem support_rectangle_w1742_s0_0 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-38016251/312500000 : ℝ)*x 0 + (1413973201/2500000000 : ℝ)*x 1 + (2482595469/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (38016251/312500000 : ℝ)^5647 ≤ (152581573431/2000000000000 : ℝ)^4623 := by
    have hnat : (38016251 : ℕ)^5647*2000000000000^4623 ≤ 152581573431^4623*312500000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38016251 312500000 152581573431 2000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1413973201/2500000000 : ℝ)^5647 ≤ (398813518723/800000000000 : ℝ)^4623 := by
    have hnat : (1413973201 : ℕ)^5647*800000000000^4623 ≤ 398813518723^4623*2500000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1413973201 2500000000 398813518723 800000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2482595469/5000000000 : ℝ)^5647 ≤ (42519231476599/100000000000000 : ℝ)^4623 := by
    have hnat : (2482595469 : ℕ)^5647*100000000000000^4623 ≤ 42519231476599^4623*5000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2482595469 5000000000 42519231476599 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-38016251/312500000 : ℝ), (1413973201/2500000000 : ℝ), (2482595469/5000000000 : ℝ)] ![(152581573431/2000000000000 : ℝ), (398813518723/800000000000 : ℝ), (42519231476599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-38016251/312500000 : ℝ)|^5647 ≤ (152581573431/2000000000000 : ℝ)^4623
        have hw : |(-38016251/312500000 : ℝ)|=(38016251/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1413973201/2500000000 : ℝ)|^5647 ≤ (398813518723/800000000000 : ℝ)^4623
        have hw : |(1413973201/2500000000 : ℝ)|=(1413973201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2482595469/5000000000 : ℝ)|^5647 ≤ (42519231476599/100000000000000 : ℝ)^4623
        have hw : |(2482595469/5000000000 : ℝ)|=(2482595469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_s0_1 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (672668697/1250000000 : ℝ)*x 0 + (-1588566471/10000000000 : ℝ)*x 1 + (39721531/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672668697/1250000000 : ℝ)^5647 ≤ (23455964253561/50000000000000 : ℝ)^4623 := by
    have hnat : (672668697 : ℕ)^5647*50000000000000^4623 ≤ 23455964253561^4623*1250000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672668697 1250000000 23455964253561 50000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1588566471/10000000000 : ℝ)^5647 ≤ (10568835434581/100000000000000 : ℝ)^4623 := by
    have hnat : (1588566471 : ℕ)^5647*100000000000000^4623 ≤ 10568835434581^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1588566471 10000000000 10568835434581 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (39721531/80000000 : ℝ)^5647 ≤ (21259618023871/50000000000000 : ℝ)^4623 := by
    have hnat : (39721531 : ℕ)^5647*50000000000000^4623 ≤ 21259618023871^4623*80000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      39721531 80000000 21259618023871 50000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672668697/1250000000 : ℝ), (-1588566471/10000000000 : ℝ), (39721531/80000000 : ℝ)] ![(23455964253561/50000000000000 : ℝ), (10568835434581/100000000000000 : ℝ), (21259618023871/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672668697/1250000000 : ℝ)|^5647 ≤ (23455964253561/50000000000000 : ℝ)^4623
        have hw : |(672668697/1250000000 : ℝ)|=(672668697/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1588566471/10000000000 : ℝ)|^5647 ≤ (10568835434581/100000000000000 : ℝ)^4623
        have hw : |(-1588566471/10000000000 : ℝ)|=(1588566471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(39721531/80000000 : ℝ)|^5647 ≤ (21259618023871/50000000000000 : ℝ)^4623
        have hw : |(39721531/80000000 : ℝ)|=(39721531/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_s0_2 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5381348351/10000000000 : ℝ)*x 0 + (4965192461/10000000000 : ℝ)*x 1 + (-1588566679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5381348351/10000000000 : ℝ)^5647 ≤ (366499339553/781250000000 : ℝ)^4623 := by
    have hnat : (5381348351 : ℕ)^5647*781250000000^4623 ≤ 366499339553^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5381348351 10000000000 366499339553 781250000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4965192461/10000000000 : ℝ)^5647 ≤ (42519247407607/100000000000000 : ℝ)^4623 := by
    have hnat : (4965192461 : ℕ)^5647*100000000000000^4623 ≤ 42519247407607^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4965192461 10000000000 42519247407607 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1588566679/10000000000 : ℝ)^5647 ≤ (528441856247/5000000000000 : ℝ)^4623 := by
    have hnat : (1588566679 : ℕ)^5647*5000000000000^4623 ≤ 528441856247^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1588566679 10000000000 528441856247 5000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5381348351/10000000000 : ℝ), (4965192461/10000000000 : ℝ), (-1588566679/10000000000 : ℝ)] ![(366499339553/781250000000 : ℝ), (42519247407607/100000000000000 : ℝ), (528441856247/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5381348351/10000000000 : ℝ)|^5647 ≤ (366499339553/781250000000 : ℝ)^4623
        have hw : |(5381348351/10000000000 : ℝ)|=(5381348351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4965192461/10000000000 : ℝ)|^5647 ≤ (42519247407607/100000000000000 : ℝ)^4623
        have hw : |(4965192461/10000000000 : ℝ)|=(4965192461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1588566679/10000000000 : ℝ)|^5647 ≤ (528441856247/5000000000000 : ℝ)^4623
        have hw : |(-1588566679/10000000000 : ℝ)|=(1588566679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_s0_3 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (797900079/2000000000 : ℝ)*x 0 + (595332729/2000000000 : ℝ)*x 1 + (1293010739/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (797900079/2000000000 : ℝ)^5647 ≤ (4068473589581/12500000000000 : ℝ)^4623 := by
    have hnat : (797900079 : ℕ)^5647*12500000000000^4623 ≤ 4068473589581^4623*2000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      797900079 2000000000 4068473589581 12500000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (595332729/2000000000 : ℝ)^5647 ≤ (1137968614117/5000000000000 : ℝ)^4623 := by
    have hnat : (595332729 : ℕ)^5647*5000000000000^4623 ≤ 1137968614117^4623*2000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      595332729 2000000000 1137968614117 5000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1293010739/2500000000 : ℝ)^5647 ≤ (8938567797107/20000000000000 : ℝ)^4623 := by
    have hnat : (1293010739 : ℕ)^5647*20000000000000^4623 ≤ 8938567797107^4623*2500000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293010739 2500000000 8938567797107 20000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(797900079/2000000000 : ℝ), (595332729/2000000000 : ℝ), (1293010739/2500000000 : ℝ)] ![(4068473589581/12500000000000 : ℝ), (1137968614117/5000000000000 : ℝ), (8938567797107/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(797900079/2000000000 : ℝ)|^5647 ≤ (4068473589581/12500000000000 : ℝ)^4623
        have hw : |(797900079/2000000000 : ℝ)|=(797900079/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(595332729/2000000000 : ℝ)|^5647 ≤ (1137968614117/5000000000000 : ℝ)^4623
        have hw : |(595332729/2000000000 : ℝ)|=(595332729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1293010739/2500000000 : ℝ)|^5647 ≤ (8938567797107/20000000000000 : ℝ)^4623
        have hw : |(1293010739/2500000000 : ℝ)|=(1293010739/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_s0_4 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-76128957/625000000 : ℝ)*x 0 + (199320571/400000000 : ℝ)*x 1 + (5637464589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (76128957/625000000 : ℝ)^5647 ≤ (191022558637/2500000000000 : ℝ)^4623 := by
    have hnat : (76128957 : ℕ)^5647*2500000000000^4623 ≤ 191022558637^4623*625000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76128957 625000000 191022558637 2500000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (199320571/400000000 : ℝ)^5647 ≤ (10676435659559/25000000000000 : ℝ)^4623 := by
    have hnat : (199320571 : ℕ)^5647*25000000000000^4623 ≤ 10676435659559^4623*400000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199320571 400000000 10676435659559 25000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5637464589/10000000000 : ℝ)^5647 ≤ (49653355003791/100000000000000 : ℝ)^4623 := by
    have hnat : (5637464589 : ℕ)^5647*100000000000000^4623 ≤ 49653355003791^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5637464589 10000000000 49653355003791 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-76128957/625000000 : ℝ), (199320571/400000000 : ℝ), (5637464589/10000000000 : ℝ)] ![(191022558637/2500000000000 : ℝ), (10676435659559/25000000000000 : ℝ), (49653355003791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-76128957/625000000 : ℝ)|^5647 ≤ (191022558637/2500000000000 : ℝ)^4623
        have hw : |(-76128957/625000000 : ℝ)|=(76128957/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(199320571/400000000 : ℝ)|^5647 ≤ (10676435659559/25000000000000 : ℝ)^4623
        have hw : |(199320571/400000000 : ℝ)|=(199320571/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5637464589/10000000000 : ℝ)|^5647 ≤ (49653355003791/100000000000000 : ℝ)^4623
        have hw : |(5637464589/10000000000 : ℝ)|=(5637464589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_s0_5 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196391517/10000000000 : ℝ)*x 0 + (-57268409/625000000 : ℝ)*x 1 + (5637465657/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196391517/10000000000 : ℝ)^5647 ≤ (44949978673457/100000000000000 : ℝ)^4623 := by
    have hnat : (5196391517 : ℕ)^5647*100000000000000^4623 ≤ 44949978673457^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196391517 10000000000 44949978673457 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (57268409/625000000 : ℝ)^5647 ≤ (1079330963597/20000000000000 : ℝ)^4623 := by
    have hnat : (57268409 : ℕ)^5647*20000000000000^4623 ≤ 1079330963597^4623*625000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57268409 625000000 1079330963597 20000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5637465657/10000000000 : ℝ)^5647 ≤ (49653366494053/100000000000000 : ℝ)^4623 := by
    have hnat : (5637465657 : ℕ)^5647*100000000000000^4623 ≤ 49653366494053^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5637465657 10000000000 49653366494053 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196391517/10000000000 : ℝ), (-57268409/625000000 : ℝ), (5637465657/10000000000 : ℝ)] ![(44949978673457/100000000000000 : ℝ), (1079330963597/20000000000000 : ℝ), (49653366494053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196391517/10000000000 : ℝ)|^5647 ≤ (44949978673457/100000000000000 : ℝ)^4623
        have hw : |(5196391517/10000000000 : ℝ)|=(5196391517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-57268409/625000000 : ℝ)|^5647 ≤ (1079330963597/20000000000000 : ℝ)^4623
        have hw : |(-57268409/625000000 : ℝ)|=(57268409/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5637465657/10000000000 : ℝ)|^5647 ≤ (49653366494053/100000000000000 : ℝ)^4623
        have hw : |(5637465657/10000000000 : ℝ)|=(5637465657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_s0_6 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (259819659/500000000 : ℝ)*x 0 + (88085373/156250000 : ℝ)*x 1 + (-91629477/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259819659/500000000 : ℝ)^5647 ≤ (44949996245157/100000000000000 : ℝ)^4623 := by
    have hnat : (259819659 : ℕ)^5647*100000000000000^4623 ≤ 44949996245157^4623*500000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259819659 500000000 44949996245157 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88085373/156250000 : ℝ)^5647 ≤ (49653347289823/100000000000000 : ℝ)^4623 := by
    have hnat : (88085373 : ℕ)^5647*100000000000000^4623 ≤ 49653347289823^4623*156250000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88085373 156250000 49653347289823 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (91629477/1000000000 : ℝ)^5647 ≤ (5396656443877/100000000000000 : ℝ)^4623 := by
    have hnat : (91629477 : ℕ)^5647*100000000000000^4623 ≤ 5396656443877^4623*1000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91629477 1000000000 5396656443877 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(259819659/500000000 : ℝ), (88085373/156250000 : ℝ), (-91629477/1000000000 : ℝ)] ![(44949996245157/100000000000000 : ℝ), (49653347289823/100000000000000 : ℝ), (5396656443877/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(259819659/500000000 : ℝ)|^5647 ≤ (44949996245157/100000000000000 : ℝ)^4623
        have hw : |(259819659/500000000 : ℝ)|=(259819659/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(88085373/156250000 : ℝ)|^5647 ≤ (49653347289823/100000000000000 : ℝ)^4623
        have hw : |(88085373/156250000 : ℝ)|=(88085373/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-91629477/1000000000 : ℝ)|^5647 ≤ (5396656443877/100000000000000 : ℝ)^4623
        have hw : |(-91629477/1000000000 : ℝ)|=(91629477/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_s0_7 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (798882357/2000000000 : ℝ)*x 0 + (5115395721/10000000000 : ℝ)*x 1 + (1517619361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (798882357/2000000000 : ℝ)^5647 ≤ (32596739594167/100000000000000 : ℝ)^4623 := by
    have hnat : (798882357 : ℕ)^5647*100000000000000^4623 ≤ 32596739594167^4623*2000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      798882357 2000000000 32596739594167 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5115395721/10000000000 : ℝ)^5647 ≤ (11023909745129/25000000000000 : ℝ)^4623 := by
    have hnat : (5115395721 : ℕ)^5647*25000000000000^4623 ≤ 11023909745129^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5115395721 10000000000 11023909745129 25000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1517619361/5000000000 : ℝ)^5647 ≤ (72836316919/312500000000 : ℝ)^4623 := by
    have hnat : (1517619361 : ℕ)^5647*312500000000^4623 ≤ 72836316919^4623*5000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1517619361 5000000000 72836316919 312500000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(798882357/2000000000 : ℝ), (5115395721/10000000000 : ℝ), (1517619361/5000000000 : ℝ)] ![(32596739594167/100000000000000 : ℝ), (11023909745129/25000000000000 : ℝ), (72836316919/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(798882357/2000000000 : ℝ)|^5647 ≤ (32596739594167/100000000000000 : ℝ)^4623
        have hw : |(798882357/2000000000 : ℝ)|=(798882357/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5115395721/10000000000 : ℝ)|^5647 ≤ (11023909745129/25000000000000 : ℝ)^4623
        have hw : |(5115395721/10000000000 : ℝ)|=(5115395721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1517619361/5000000000 : ℝ)|^5647 ≤ (72836316919/312500000000 : ℝ)^4623
        have hw : |(1517619361/5000000000 : ℝ)|=(1517619361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1742_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (104462069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3193/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10643/50000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (0 : ℝ) ^ (5631/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5631 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5631*1^1024 ≤ 0^1024*1^5631 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5631 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5631 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5631/1024 : ℝ) ≤ (81026779662592089/12500000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5631 ≤ (81026779662592089/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5631*12500000000000000000^1024 ≤ 81026779662592089^1024*5^5631 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 81026779662592089 12500000000000000000 5631 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (81026779662592089/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5631 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5631/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5631 := by
      have hnat : (1 : ℕ)^1024*1^5631 ≤ 1^5631*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5631 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12581026779662592089/12500000000000000000 : ℝ) ≤ (5005878335573629/5000000000000000 : ℝ) ^ (5631/1024 : ℝ) := by
    have hpowers : (12581026779662592089/12500000000000000000 : ℝ)^1024 ≤ (5005878335573629/5000000000000000 : ℝ)^5631 := by
      have hnat : (12581026779662592089 : ℕ)^1024*5000000000000000^5631 ≤ 5005878335573629^5631*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12581026779662592089 12500000000000000000 5005878335573629 5000000000000000 1024 5631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005878335573629/5000000000000000 : ℝ)) (X := (12581026779662592089/12500000000000000000 : ℝ)) (by norm_num) 5631 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6331026779662592089/6250000000000000000 : ℝ) ≤ (2505878335573629/2500000000000000 : ℝ) ^ (5631/1024 : ℝ) := by
    have hpowers : (6331026779662592089/6250000000000000000 : ℝ)^1024 ≤ (2505878335573629/2500000000000000 : ℝ)^5631 := by
      have hnat : (6331026779662592089 : ℕ)^1024*2500000000000000^5631 ≤ 2505878335573629^5631*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6331026779662592089 6250000000000000000 2505878335573629 2500000000000000 1024 5631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2505878335573629/2500000000000000 : ℝ)) (X := (6331026779662592089/6250000000000000000 : ℝ)) (by norm_num) 5631 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(5878335573629/2000000000000000 : ℝ)*(0 : ℝ))^(5631/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5878335573629/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(81026779662592089/12500000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(5878335573629/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5631/1024 : ℝ) := by
    rw [show (1 : ℝ)+(5878335573629/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5005878335573629/5000000000000000 : ℝ) by norm_num, show 1+(81026779662592089/12500000000000000000 : ℝ)+(0 : ℝ)=(12581026779662592089/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(81026779662592089/12500000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(5878335573629/2000000000000000 : ℝ)*(2/5 : ℝ))^(5631/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(5878335573629/2000000000000000 : ℝ)*(2/5 : ℝ)=(2505878335573629/2500000000000000 : ℝ) by norm_num, show 1+2*(81026779662592089/12500000000000000000 : ℝ)=(6331026779662592089/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(5878335573629/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5631/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5878335573629/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(5878335573629/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5631/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5878335573629/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(5878335573629/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5631/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5878335573629/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-38016251/312500000 : ℝ)*X 0 0+(1413973201/2500000000 : ℝ)*X 0 1+(2482595469/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((672668697/1250000000 : ℝ)*X 1 0+(-1588566471/10000000000 : ℝ)*X 1 1+(39721531/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5381348351/10000000000 : ℝ)*X 2 0+(4965192461/10000000000 : ℝ)*X 2 1+(-1588566679/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((797900079/2000000000 : ℝ)*X 0 0+(595332729/2000000000 : ℝ)*X 0 1+(1293010739/2500000000 : ℝ)*X 0 2+(797900079/2000000000 : ℝ)*X 1 0+(595332729/2000000000 : ℝ)*X 1 1+(1293010739/2500000000 : ℝ)*X 1 2+(797900079/2000000000 : ℝ)*X 2 0+(595332729/2000000000 : ℝ)*X 2 1+(1293010739/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-76128957/625000000 : ℝ)*X 0 0+(199320571/400000000 : ℝ)*X 0 1+(5637464589/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5196391517/10000000000 : ℝ)*X 1 0+(-57268409/625000000 : ℝ)*X 1 1+(5637465657/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((259819659/500000000 : ℝ)*X 2 0+(88085373/156250000 : ℝ)*X 2 1+(-91629477/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((798882357/2000000000 : ℝ)*X 0 0+(5115395721/10000000000 : ℝ)*X 0 1+(1517619361/5000000000 : ℝ)*X 0 2+(798882357/2000000000 : ℝ)*X 1 0+(5115395721/10000000000 : ℝ)*X 1 1+(1517619361/5000000000 : ℝ)*X 1 2+(798882357/2000000000 : ℝ)*X 2 0+(5115395721/10000000000 : ℝ)*X 2 1+(1517619361/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (25615784592652661768913/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1203363/25000000000000 : ℝ)*(base1) + (207131589/25000000000000 : ℝ)*(base19) + (249474679/50000000000000 : ℝ)*(base23) + (22844149/10000000000000 : ℝ)*(upper3) + (298773/390625000000 : ℝ)*(upper5) + (190331618345399/20000000000000 : ℝ)*(major0) + (190331618345399/20000000000000 : ℝ)*(major1) + (190331618345399/20000000000000 : ℝ)*(major2) + (90488015834729/6250000000000 : ℝ)*(sp0) + (361952783141953/25000000000000 : ℝ)*(sp1) + (144781146214481/10000000000000 : ℝ)*(sp2) + (56937869091873/12500000000000 : ℝ)*(sp3) + (928137989/25000000000000 : ℝ)*(sp4) + (1179425433/100000000000000 : ℝ)*(sp7) + (455504136973869/100000000000000 : ℝ)*(f.failure) + (180976495136771/12500000000000 : ℝ)*(f.sum) + (14367576582971/20000000000000000000000000000 : ℝ)*base65 + (490935187277029/40000000000000000000000000000 : ℝ)*base68 + (48735411957029/40000000000000000000000000000 : ℝ)*base70 + (223057253997029/40000000000000000000000000000 : ℝ)*base72 + (85513430537029/20000000000000000000000000000 : ℝ)*base74 + (208277915317029/40000000000000000000000000000 : ℝ)*base76 + (115827677917029/40000000000000000000000000000 : ℝ)*base78 + (299129733437029/40000000000000000000000000000 : ℝ)*base80 + (60002451082971/20000000000000000000000000000 : ℝ)*base81 + (4674961/5000000000000000000000 : ℝ)*base89 + (4674961/5000000000000000000000 : ℝ)*base91 + (4674961/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31303201528628872442037/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (454089713/100000000000000 : ℝ)*(base19) + (969254023/100000000000000 : ℝ)*(base23) + (699722579/100000000000000 : ℝ)*(base32) + (140989559/100000000000000 : ℝ)*(base37) + (111797797/50000000000000 : ℝ)*(upper3) + (100436518266049/10000000000000 : ℝ)*(major0) + (100436518266049/10000000000000 : ℝ)*(major1) + (100436518266049/10000000000000 : ℝ)*(major2) + (409632759/20000000000000 : ℝ)*(sp1) + (2783165619/100000000000000 : ℝ)*(sp2) + (1527997950065179/100000000000000 : ℝ)*(sp4) + (1527995447811671/100000000000000 : ℝ)*(sp5) + (1527994197645537/100000000000000 : ℝ)*(sp6) + (30045697322977/6250000000000 : ℝ)*(sp7) + (480731997879771/100000000000000 : ℝ)*(f.failure) + (1527997950065179/100000000000000 : ℝ)*(f.sum) + (15357547701821/10000000000000000000000000000 : ℝ)*base65 + (327686192481821/20000000000000000000000000000 : ℝ)*base67 + (127766995721821/20000000000000000000000000000 : ℝ)*base69 + (161062071481821/20000000000000000000000000000 : ℝ)*base71 + (49859228391821/10000000000000000000000000000 : ℝ)*base73 + (253104904901821/20000000000000000000000000000 : ℝ)*base75 + (127262349441821/20000000000000000000000000000 : ℝ)*base77 + (380980044521821/20000000000000000000000000000 : ℝ)*base79 + (26742104708179/10000000000000000000000000000 : ℝ)*base82 + (8093801/5000000000000000000000 : ℝ)*base90 + (8093801/5000000000000000000000 : ℝ)*base92 + (8093801/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1742_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (104462069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3193/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10643/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1742_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1742_s1_0 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1266783331/10000000000 : ℝ)*x 0 + (2756400281/5000000000 : ℝ)*x 1 + (63435173/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1266783331/10000000000 : ℝ)^5647 ≤ (4007927391951/50000000000000 : ℝ)^4623 := by
    have hnat : (1266783331 : ℕ)^5647*50000000000000^4623 ≤ 4007927391951^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1266783331 10000000000 4007927391951 50000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2756400281/5000000000 : ℝ)^5647 ≤ (12078859856399/25000000000000 : ℝ)^4623 := by
    have hnat : (2756400281 : ℕ)^5647*25000000000000^4623 ≤ 12078859856399^4623*5000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2756400281 5000000000 12078859856399 25000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (63435173/125000000 : ℝ)^5647 ≤ (10917176443059/25000000000000 : ℝ)^4623 := by
    have hnat : (63435173 : ℕ)^5647*25000000000000^4623 ≤ 10917176443059^4623*125000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63435173 125000000 10917176443059 25000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1266783331/10000000000 : ℝ), (2756400281/5000000000 : ℝ), (63435173/125000000 : ℝ)] ![(4007927391951/50000000000000 : ℝ), (12078859856399/25000000000000 : ℝ), (10917176443059/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1266783331/10000000000 : ℝ)|^5647 ≤ (4007927391951/50000000000000 : ℝ)^4623
        have hw : |(-1266783331/10000000000 : ℝ)|=(1266783331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2756400281/5000000000 : ℝ)|^5647 ≤ (12078859856399/25000000000000 : ℝ)^4623
        have hw : |(2756400281/5000000000 : ℝ)|=(2756400281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(63435173/125000000 : ℝ)|^5647 ≤ (10917176443059/25000000000000 : ℝ)^4623
        have hw : |(63435173/125000000 : ℝ)|=(63435173/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_s1_1 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534322339/1000000000 : ℝ)*x 0 + (-1496440061/10000000000 : ℝ)*x 1 + (1014962743/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534322339/1000000000 : ℝ)^5647 ≤ (4650626325921/10000000000000 : ℝ)^4623 := by
    have hnat : (534322339 : ℕ)^5647*10000000000000^4623 ≤ 4650626325921^4623*1000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534322339 1000000000 4650626325921 10000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1496440061/10000000000 : ℝ)^5647 ≤ (9825032268811/100000000000000 : ℝ)^4623 := by
    have hnat : (1496440061 : ℕ)^5647*100000000000000^4623 ≤ 9825032268811^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1496440061 10000000000 9825032268811 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1014962743/2000000000 : ℝ)^5647 ≤ (43668704458361/100000000000000 : ℝ)^4623 := by
    have hnat : (1014962743 : ℕ)^5647*100000000000000^4623 ≤ 43668704458361^4623*2000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014962743 2000000000 43668704458361 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534322339/1000000000 : ℝ), (-1496440061/10000000000 : ℝ), (1014962743/2000000000 : ℝ)] ![(4650626325921/10000000000000 : ℝ), (9825032268811/100000000000000 : ℝ), (43668704458361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534322339/1000000000 : ℝ)|^5647 ≤ (4650626325921/10000000000000 : ℝ)^4623
        have hw : |(534322339/1000000000 : ℝ)|=(534322339/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1496440061/10000000000 : ℝ)|^5647 ≤ (9825032268811/100000000000000 : ℝ)^4623
        have hw : |(-1496440061/10000000000 : ℝ)|=(1496440061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1014962743/2000000000 : ℝ)|^5647 ≤ (43668704458361/100000000000000 : ℝ)^4623
        have hw : |(1014962743/2000000000 : ℝ)|=(1014962743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_s1_2 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2671611479/5000000000 : ℝ)*x 0 + (5074814041/10000000000 : ℝ)*x 1 + (-748220103/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2671611479/5000000000 : ℝ)^5647 ≤ (46506258666323/100000000000000 : ℝ)^4623 := by
    have hnat : (2671611479 : ℕ)^5647*100000000000000^4623 ≤ 46506258666323^4623*5000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2671611479 5000000000 46506258666323 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5074814041/10000000000 : ℝ)^5647 ≤ (10917176971237/25000000000000 : ℝ)^4623 := by
    have hnat : (5074814041 : ℕ)^5647*25000000000000^4623 ≤ 10917176971237^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5074814041 10000000000 10917176971237 25000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (748220103/5000000000 : ℝ)^5647 ≤ (1965006686339/20000000000000 : ℝ)^4623 := by
    have hnat : (748220103 : ℕ)^5647*20000000000000^4623 ≤ 1965006686339^4623*5000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748220103 5000000000 1965006686339 20000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2671611479/5000000000 : ℝ), (5074814041/10000000000 : ℝ), (-748220103/5000000000 : ℝ)] ![(46506258666323/100000000000000 : ℝ), (10917176971237/25000000000000 : ℝ), (1965006686339/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2671611479/5000000000 : ℝ)|^5647 ≤ (46506258666323/100000000000000 : ℝ)^4623
        have hw : |(2671611479/5000000000 : ℝ)|=(2671611479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5074814041/10000000000 : ℝ)|^5647 ≤ (10917176971237/25000000000000 : ℝ)^4623
        have hw : |(5074814041/10000000000 : ℝ)|=(5074814041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-748220103/5000000000 : ℝ)|^5647 ≤ (1965006686339/20000000000000 : ℝ)^4623
        have hw : |(-748220103/5000000000 : ℝ)|=(748220103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_s1_3 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1009183063/2500000000 : ℝ)*x 0 + (3374559887/10000000000 : ℝ)*x 1 + (4766691901/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1009183063/2500000000 : ℝ)^5647 ≤ (8254772661741/25000000000000 : ℝ)^4623 := by
    have hnat : (1009183063 : ℕ)^5647*25000000000000^4623 ≤ 8254772661741^4623*2500000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009183063 2500000000 8254772661741 25000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3374559887/10000000000 : ℝ)^5647 ≤ (663218578823/2500000000000 : ℝ)^4623 := by
    have hnat : (3374559887 : ℕ)^5647*2500000000000^4623 ≤ 663218578823^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3374559887 10000000000 663218578823 2500000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4766691901/10000000000 : ℝ)^5647 ≤ (5056520772293/12500000000000 : ℝ)^4623 := by
    have hnat : (4766691901 : ℕ)^5647*12500000000000^4623 ≤ 5056520772293^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4766691901 10000000000 5056520772293 12500000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1009183063/2500000000 : ℝ), (3374559887/10000000000 : ℝ), (4766691901/10000000000 : ℝ)] ![(8254772661741/25000000000000 : ℝ), (663218578823/2500000000000 : ℝ), (5056520772293/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1009183063/2500000000 : ℝ)|^5647 ≤ (8254772661741/25000000000000 : ℝ)^4623
        have hw : |(1009183063/2500000000 : ℝ)|=(1009183063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3374559887/10000000000 : ℝ)|^5647 ≤ (663218578823/2500000000000 : ℝ)^4623
        have hw : |(3374559887/10000000000 : ℝ)|=(3374559887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4766691901/10000000000 : ℝ)|^5647 ≤ (5056520772293/12500000000000 : ℝ)^4623
        have hw : |(4766691901/10000000000 : ℝ)|=(4766691901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_s1_4 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-316793463/2500000000 : ℝ)*x 0 + (317623989/625000000 : ℝ)*x 1 + (550547671/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (316793463/2500000000 : ℝ)^5647 ≤ (250589792171/3125000000000 : ℝ)^4623 := by
    have hnat : (316793463 : ℕ)^5647*3125000000000^4623 ≤ 250589792171^4623*2500000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316793463 2500000000 250589792171 3125000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (317623989/625000000 : ℝ)^5647 ≤ (1367002539789/3125000000000 : ℝ)^4623 := by
    have hnat : (317623989 : ℕ)^5647*3125000000000^4623 ≤ 1367002539789^4623*625000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      317623989 625000000 1367002539789 3125000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550547671/1000000000 : ℝ)^5647 ≤ (48237045361417/100000000000000 : ℝ)^4623 := by
    have hnat : (550547671 : ℕ)^5647*100000000000000^4623 ≤ 48237045361417^4623*1000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550547671 1000000000 48237045361417 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-316793463/2500000000 : ℝ), (317623989/625000000 : ℝ), (550547671/1000000000 : ℝ)] ![(250589792171/3125000000000 : ℝ), (1367002539789/3125000000000 : ℝ), (48237045361417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-316793463/2500000000 : ℝ)|^5647 ≤ (250589792171/3125000000000 : ℝ)^4623
        have hw : |(-316793463/2500000000 : ℝ)|=(316793463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(317623989/625000000 : ℝ)|^5647 ≤ (1367002539789/3125000000000 : ℝ)^4623
        have hw : |(317623989/625000000 : ℝ)|=(317623989/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(550547671/1000000000 : ℝ)|^5647 ≤ (48237045361417/100000000000000 : ℝ)^4623
        have hw : |(550547671/1000000000 : ℝ)|=(550547671/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_s1_5 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5226869501/10000000000 : ℝ)*x 0 + (-1065776799/10000000000 : ℝ)*x 1 + (2752738543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5226869501/10000000000 : ℝ)^5647 ≤ (22636113007763/50000000000000 : ℝ)^4623 := by
    have hnat : (5226869501 : ℕ)^5647*50000000000000^4623 ≤ 22636113007763^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226869501 10000000000 22636113007763 50000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1065776799/10000000000 : ℝ)^5647 ≤ (6490724592621/100000000000000 : ℝ)^4623 := by
    have hnat : (1065776799 : ℕ)^5647*100000000000000^4623 ≤ 6490724592621^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065776799 10000000000 6490724592621 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2752738543/5000000000 : ℝ)^5647 ≤ (24118524692753/50000000000000 : ℝ)^4623 := by
    have hnat : (2752738543 : ℕ)^5647*50000000000000^4623 ≤ 24118524692753^4623*5000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2752738543 5000000000 24118524692753 50000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5226869501/10000000000 : ℝ), (-1065776799/10000000000 : ℝ), (2752738543/5000000000 : ℝ)] ![(22636113007763/50000000000000 : ℝ), (6490724592621/100000000000000 : ℝ), (24118524692753/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5226869501/10000000000 : ℝ)|^5647 ≤ (22636113007763/50000000000000 : ℝ)^4623
        have hw : |(5226869501/10000000000 : ℝ)|=(5226869501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1065776799/10000000000 : ℝ)|^5647 ≤ (6490724592621/100000000000000 : ℝ)^4623
        have hw : |(-1065776799/10000000000 : ℝ)|=(1065776799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2752738543/5000000000 : ℝ)|^5647 ≤ (24118524692753/50000000000000 : ℝ)^4623
        have hw : |(2752738543/5000000000 : ℝ)|=(2752738543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_s1_6 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (653358659/1250000000 : ℝ)*x 0 + (1376369299/2500000000 : ℝ)*x 1 + (-213155393/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (653358659/1250000000 : ℝ)^5647 ≤ (22636111796357/50000000000000 : ℝ)^4623 := by
    have hnat : (653358659 : ℕ)^5647*50000000000000^4623 ≤ 22636111796357^4623*1250000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653358659 1250000000 22636111796357 50000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1376369299/2500000000 : ℝ)^5647 ≤ (24118525281383/50000000000000 : ℝ)^4623 := by
    have hnat : (1376369299 : ℕ)^5647*50000000000000^4623 ≤ 24118525281383^4623*2500000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376369299 2500000000 24118525281383 50000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (213155393/2000000000 : ℝ)^5647 ≤ (6490725827513/100000000000000 : ℝ)^4623 := by
    have hnat : (213155393 : ℕ)^5647*100000000000000^4623 ≤ 6490725827513^4623*2000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213155393 2000000000 6490725827513 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(653358659/1250000000 : ℝ), (1376369299/2500000000 : ℝ), (-213155393/2000000000 : ℝ)] ![(22636111796357/50000000000000 : ℝ), (24118525281383/50000000000000 : ℝ), (6490725827513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(653358659/1250000000 : ℝ)|^5647 ≤ (22636111796357/50000000000000 : ℝ)^4623
        have hw : |(653358659/1250000000 : ℝ)|=(653358659/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1376369299/2500000000 : ℝ)|^5647 ≤ (24118525281383/50000000000000 : ℝ)^4623
        have hw : |(1376369299/2500000000 : ℝ)|=(1376369299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-213155393/2000000000 : ℝ)|^5647 ≤ (6490725827513/100000000000000 : ℝ)^4623
        have hw : |(-213155393/2000000000 : ℝ)|=(213155393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_s1_7 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (807594809/2000000000 : ℝ)*x 0 + (29649399/62500000 : ℝ)*x 1 + (84945921/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (807594809/2000000000 : ℝ)^5647 ≤ (33031498397707/100000000000000 : ℝ)^4623 := by
    have hnat : (807594809 : ℕ)^5647*100000000000000^4623 ≤ 33031498397707^4623*2000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      807594809 2000000000 33031498397707 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (29649399/62500000 : ℝ)^5647 ≤ (5027008293279/12500000000000 : ℝ)^4623 := by
    have hnat : (29649399 : ℕ)^5647*12500000000000^4623 ≤ 5027008293279^4623*62500000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29649399 62500000 5027008293279 12500000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84945921/250000000 : ℝ)^5647 ≤ (6688108808849/25000000000000 : ℝ)^4623 := by
    have hnat : (84945921 : ℕ)^5647*25000000000000^4623 ≤ 6688108808849^4623*250000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84945921 250000000 6688108808849 25000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(807594809/2000000000 : ℝ), (29649399/62500000 : ℝ), (84945921/250000000 : ℝ)] ![(33031498397707/100000000000000 : ℝ), (5027008293279/12500000000000 : ℝ), (6688108808849/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(807594809/2000000000 : ℝ)|^5647 ≤ (33031498397707/100000000000000 : ℝ)^4623
        have hw : |(807594809/2000000000 : ℝ)|=(807594809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(29649399/62500000 : ℝ)|^5647 ≤ (5027008293279/12500000000000 : ℝ)^4623
        have hw : |(29649399/62500000 : ℝ)|=(29649399/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84945921/250000000 : ℝ)|^5647 ≤ (6688108808849/25000000000000 : ℝ)^4623
        have hw : |(84945921/250000000 : ℝ)|=(84945921/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1742_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (104462069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10643/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3193/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (8847/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18233/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10643/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3193/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10643/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3193/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10643/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3193/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10643/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3193/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10643/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3193/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10643/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3193/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3193/50000 : ℝ) ^ (5631/1024 : ℝ) ≤ (26910749695117/100000000000000000000 : ℝ) := by
    have hpowers : (3193/50000 : ℝ)^5631 ≤ (26910749695117/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3193 : ℕ)^5631*100000000000000000000^1024 ≤ 26910749695117^1024*50000^5631 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3193 50000 26910749695117 100000000000000000000 5631 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3193/50000 : ℝ)) (X := (26910749695117/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5631 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (10643/50000 : ℝ) ^ (5631/1024 : ℝ) ≤ (5047931870368897/25000000000000000000 : ℝ) := by
    have hpowers : (10643/50000 : ℝ)^5631 ≤ (5047931870368897/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10643 : ℕ)^5631*25000000000000000000^1024 ≤ 5047931870368897^1024*50000^5631 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10643 50000 5047931870368897 25000000000000000000 5631 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10643/50000 : ℝ)) (X := (5047931870368897/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5631 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000026910749695117/50000000000000000000 : ℝ) ≤ (2500000244686571/2500000000000000 : ℝ) ^ (5631/1024 : ℝ) := by
    have hpowers : (50000026910749695117/50000000000000000000 : ℝ)^1024 ≤ (2500000244686571/2500000000000000 : ℝ)^5631 := by
      have hnat : (50000026910749695117 : ℕ)^1024*2500000000000000^5631 ≤ 2500000244686571^5631*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000026910749695117 50000000000000000000 2500000244686571 2500000000000000 1024 5631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000244686571/2500000000000000 : ℝ)) (X := (50000026910749695117/50000000000000000000 : ℝ)) (by norm_num) 5631 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20004043727646234141/20000000000000000000 : ℝ) ≤ (10000367646481153/10000000000000000 : ℝ) ^ (5631/1024 : ℝ) := by
    have hpowers : (20004043727646234141/20000000000000000000 : ℝ)^1024 ≤ (10000367646481153/10000000000000000 : ℝ)^5631 := by
      have hnat : (20004043727646234141 : ℕ)^1024*10000000000000000^5631 ≤ 10000367646481153^5631*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20004043727646234141 20000000000000000000 10000367646481153 10000000000000000 1024 5631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000367646481153/10000000000000000 : ℝ)) (X := (20004043727646234141/20000000000000000000 : ℝ)) (by norm_num) 5631 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505047931870368897/12500000000000000000 : ℝ) ≤ (5000367157108011/5000000000000000 : ℝ) ^ (5631/1024 : ℝ) := by
    have hpowers : (12505047931870368897/12500000000000000000 : ℝ)^1024 ≤ (5000367157108011/5000000000000000 : ℝ)^5631 := by
      have hnat : (12505047931870368897 : ℕ)^1024*5000000000000000^5631 ≤ 5000367157108011^5631*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505047931870368897 12500000000000000000 5000367157108011 5000000000000000 1024 5631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000367157108011/5000000000000000 : ℝ)) (X := (12505047931870368897/12500000000000000000 : ℝ)) (by norm_num) 5631 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(26910749695117/100000000000000000000 : ℝ) ≤ ((249992166951358867/250000000000000000 : ℝ)+2*(2460857281/10000000000000 : ℝ)*(3193/50000 : ℝ))^(5631/1024 : ℝ) := by
    rw [show (249992166951358867/250000000000000000 : ℝ)+2*(2460857281/10000000000000 : ℝ)*(3193/50000 : ℝ)=(2500000244686571/2500000000000000 : ℝ) by norm_num, show 1+2*(26910749695117/100000000000000000000 : ℝ)=(50000026910749695117/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5047931870368897/25000000000000000000 : ℝ)+(26910749695117/100000000000000000000 : ℝ) ≤ ((249992166951358867/250000000000000000 : ℝ)+(2460857281/10000000000000 : ℝ)*((10643/50000 : ℝ)+(3193/50000 : ℝ)))^(5631/1024 : ℝ) := by
    rw [show (249992166951358867/250000000000000000 : ℝ)+(2460857281/10000000000000 : ℝ)*((10643/50000 : ℝ)+(3193/50000 : ℝ))=(10000367646481153/10000000000000000 : ℝ) by norm_num, show 1+(5047931870368897/25000000000000000000 : ℝ)+(26910749695117/100000000000000000000 : ℝ)=(20004043727646234141/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5047931870368897/25000000000000000000 : ℝ) ≤ ((249992166951358867/250000000000000000 : ℝ)+2*(2460857281/10000000000000 : ℝ)*(10643/50000 : ℝ))^(5631/1024 : ℝ) := by
    rw [show (249992166951358867/250000000000000000 : ℝ)+2*(2460857281/10000000000000 : ℝ)*(10643/50000 : ℝ)=(5000367157108011/5000000000000000 : ℝ) by norm_num, show 1+2*(5047931870368897/25000000000000000000 : ℝ)=(12505047931870368897/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (249992166951358867/250000000000000000 : ℝ)*(X 1 0+X 2 0)+(2460857281/10000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5631/1024 : ℝ)) (lo := (3193/50000 : ℝ)) (hi := (10643/50000 : ℝ)) (c := (249992166951358867/250000000000000000 : ℝ)) (alpha := (2460857281/10000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (249992166951358867/250000000000000000 : ℝ)*(X 0 1+X 2 1)+(2460857281/10000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5631/1024 : ℝ)) (lo := (3193/50000 : ℝ)) (hi := (10643/50000 : ℝ)) (c := (249992166951358867/250000000000000000 : ℝ)) (alpha := (2460857281/10000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (249992166951358867/250000000000000000 : ℝ)*(X 0 2+X 1 2)+(2460857281/10000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5631/1024 : ℝ)) (lo := (3193/50000 : ℝ)) (hi := (10643/50000 : ℝ)) (c := (249992166951358867/250000000000000000 : ℝ)) (alpha := (2460857281/10000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1266783331/10000000000 : ℝ)*X 0 0+(2756400281/5000000000 : ℝ)*X 0 1+(63435173/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534322339/1000000000 : ℝ)*X 1 0+(-1496440061/10000000000 : ℝ)*X 1 1+(1014962743/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2671611479/5000000000 : ℝ)*X 2 0+(5074814041/10000000000 : ℝ)*X 2 1+(-748220103/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1009183063/2500000000 : ℝ)*X 0 0+(3374559887/10000000000 : ℝ)*X 0 1+(4766691901/10000000000 : ℝ)*X 0 2+(1009183063/2500000000 : ℝ)*X 1 0+(3374559887/10000000000 : ℝ)*X 1 1+(4766691901/10000000000 : ℝ)*X 1 2+(1009183063/2500000000 : ℝ)*X 2 0+(3374559887/10000000000 : ℝ)*X 2 1+(4766691901/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-316793463/2500000000 : ℝ)*X 0 0+(317623989/625000000 : ℝ)*X 0 1+(550547671/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5226869501/10000000000 : ℝ)*X 1 0+(-1065776799/10000000000 : ℝ)*X 1 1+(2752738543/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((653358659/1250000000 : ℝ)*X 2 0+(1376369299/2500000000 : ℝ)*X 2 1+(-213155393/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((807594809/2000000000 : ℝ)*X 0 0+(29649399/62500000 : ℝ)*X 0 1+(84945921/250000000 : ℝ)*X 0 2+(807594809/2000000000 : ℝ)*X 1 0+(29649399/62500000 : ℝ)*X 1 1+(84945921/250000000 : ℝ)*X 1 2+(807594809/2000000000 : ℝ)*X 2 0+(29649399/62500000 : ℝ)*X 2 1+(84945921/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16105188812379947338527633/1562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1593121731/100000000000000 : ℝ)*(base19) + (1243009179/100000000000000 : ℝ)*(base23) + (17687777/20000000000000 : ℝ)*(lower2) + (62657919/20000000000000 : ℝ)*(upper3) + (8733787/10000000000000 : ℝ)*(upper5) + (375190895194833/25000000000000 : ℝ)*(major0) + (375190895194833/25000000000000 : ℝ)*(major1) + (375190895194833/25000000000000 : ℝ)*(major2) + (142699193782969/6250000000000 : ℝ)*(sp0) + (570798947380493/25000000000000 : ℝ)*(sp1) + (570799034908631/25000000000000 : ℝ)*(sp2) + (179581372048621/25000000000000 : ℝ)*(sp3) + (5141058099/50000000000000 : ℝ)*(sp4) + (3947143109/100000000000000 : ℝ)*(sp7) + (89791179417199/12500000000000 : ℝ)*(f.failure) + (2283197382643703/100000000000000 : ℝ)*(f.sum) + (38962510013/31250000000000000000000000 : ℝ)*base66 + (11616285881040789/6250000000000000000000000000000 : ℝ)*base68 + (27528255893959211/6250000000000000000000000000000 : ℝ)*base69 + (34563090162290789/6250000000000000000000000000000 : ℝ)*base72 + (716696067927/125000000000000000000000000 : ℝ)*base74 + (38702006856040789/6250000000000000000000000000000 : ℝ)*base76 + (1168570862290789/6250000000000000000000000000000 : ℝ)*base78 + (9938242656040789/6250000000000000000000000000000 : ℝ)*base80 + (468390583427/125000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (3275269/625000000000000000000 : ℝ)*base90 + (3275269/625000000000000000000 : ℝ)*base92 + (3275269/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3573749382289777782351/250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1879356321/100000000000000 : ℝ)*(base19) + (1055792003/50000000000000 : ℝ)*(base23) + (22839077/6250000000000 : ℝ)*(upper3) + (36505209/25000000000000 : ℝ)*(lower4) + (55998763/25000000000000 : ℝ)*(upper5) + (776054147645157/50000000000000 : ℝ)*(major0) + (776054147645157/50000000000000 : ℝ)*(major1) + (776054147645157/50000000000000 : ℝ)*(major2) + (6594954437/50000000000000 : ℝ)*(sp1) + (785988141/5000000000000 : ℝ)*(sp2) + (2361310909278417/100000000000000 : ℝ)*(sp4) + (1180647920006611/50000000000000 : ℝ)*(sp5) + (236129307793159/10000000000000 : ℝ)*(sp6) + (46431575300143/6250000000000 : ℝ)*(sp7) + (46431575300143/6250000000000 : ℝ)*(f.failure) + (2361310909278417/100000000000000 : ℝ)*(f.sum) + (688957830883/250000000000000000000000000 : ℝ)*base66 + (66124301365517881/12500000000000000000000000000000 : ℝ)*base68 + (101261380359482119/12500000000000000000000000000000 : ℝ)*base69 + (103366895290517881/12500000000000000000000000000000 : ℝ)*base72 + (323929218883/250000000000000000000000000 : ℝ)*base74 + (40416993790517881/12500000000000000000000000000000 : ℝ)*base76 + (19207867734482119/12500000000000000000000000000000 : ℝ)*base77 + (21220065484482119/12500000000000000000000000000000 : ℝ)*base79 + (837876675617/250000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2525867/312500000000000000000 : ℝ)*base89 + (2525867/312500000000000000000 : ℝ)*base91 + (2525867/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1742_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (104462069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10643/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3193/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8847/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18233/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1742_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1742_s2_0 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-15852971/125000000 : ℝ)*x 0 + (2754075641/5000000000 : ℝ)*x 1 + (5078478823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (15852971/125000000 : ℝ)^5647 ≤ (8027097344363/100000000000000 : ℝ)^4623 := by
    have hnat : (15852971 : ℕ)^5647*100000000000000^4623 ≤ 8027097344363^4623*125000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15852971 125000000 8027097344363 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2754075641/5000000000 : ℝ)^5647 ≤ (1206641778519/2500000000000 : ℝ)^4623 := by
    have hnat : (2754075641 : ℕ)^5647*2500000000000^4623 ≤ 1206641778519^4623*5000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754075641 5000000000 1206641778519 2500000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5078478823/10000000000 : ℝ)^5647 ≤ (174828925979/400000000000 : ℝ)^4623 := by
    have hnat : (5078478823 : ℕ)^5647*400000000000^4623 ≤ 174828925979^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5078478823 10000000000 174828925979 400000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-15852971/125000000 : ℝ), (2754075641/5000000000 : ℝ), (5078478823/10000000000 : ℝ)] ![(8027097344363/100000000000000 : ℝ), (1206641778519/2500000000000 : ℝ), (174828925979/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-15852971/125000000 : ℝ)|^5647 ≤ (8027097344363/100000000000000 : ℝ)^4623
        have hw : |(-15852971/125000000 : ℝ)|=(15852971/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2754075641/5000000000 : ℝ)|^5647 ≤ (1206641778519/2500000000000 : ℝ)^4623
        have hw : |(2754075641/5000000000 : ℝ)|=(2754075641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5078478823/10000000000 : ℝ)|^5647 ≤ (174828925979/400000000000 : ℝ)^4623
        have hw : |(5078478823/10000000000 : ℝ)|=(5078478823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_s2_1 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5341940713/10000000000 : ℝ)*x 0 + (-93333479/625000000 : ℝ)*x 1 + (2539239451/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5341940713/10000000000 : ℝ)^5647 ≤ (11623156651717/25000000000000 : ℝ)^4623 := by
    have hnat : (5341940713 : ℕ)^5647*25000000000000^4623 ≤ 11623156651717^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5341940713 10000000000 11623156651717 25000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (93333479/625000000 : ℝ)^5647 ≤ (9800141061477/100000000000000 : ℝ)^4623 := by
    have hnat : (93333479 : ℕ)^5647*100000000000000^4623 ≤ 9800141061477^4623*625000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93333479 625000000 9800141061477 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2539239451/5000000000 : ℝ)^5647 ≤ (10926808081313/25000000000000 : ℝ)^4623 := by
    have hnat : (2539239451 : ℕ)^5647*25000000000000^4623 ≤ 10926808081313^4623*5000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539239451 5000000000 10926808081313 25000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5341940713/10000000000 : ℝ), (-93333479/625000000 : ℝ), (2539239451/5000000000 : ℝ)] ![(11623156651717/25000000000000 : ℝ), (9800141061477/100000000000000 : ℝ), (10926808081313/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5341940713/10000000000 : ℝ)|^5647 ≤ (11623156651717/25000000000000 : ℝ)^4623
        have hw : |(5341940713/10000000000 : ℝ)|=(5341940713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-93333479/625000000 : ℝ)|^5647 ≤ (9800141061477/100000000000000 : ℝ)^4623
        have hw : |(-93333479/625000000 : ℝ)|=(93333479/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2539239451/5000000000 : ℝ)|^5647 ≤ (10926808081313/25000000000000 : ℝ)^4623
        have hw : |(2539239451/5000000000 : ℝ)|=(2539239451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_s2_2 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1043348/1953125 : ℝ)*x 0 + (2539239099/5000000000 : ℝ)*x 1 + (-1493335197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1043348/1953125 : ℝ)^5647 ≤ (2905789858603/6250000000000 : ℝ)^4623 := by
    have hnat : (1043348 : ℕ)^5647*6250000000000^4623 ≤ 2905789858603^4623*1953125^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043348 1953125 2905789858603 6250000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2539239099/5000000000 : ℝ)^5647 ≤ (43707224924323/100000000000000 : ℝ)^4623 := by
    have hnat : (2539239099 : ℕ)^5647*100000000000000^4623 ≤ 43707224924323^4623*5000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539239099 5000000000 43707224924323 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1493335197/10000000000 : ℝ)^5647 ≤ (980013731791/10000000000000 : ℝ)^4623 := by
    have hnat : (1493335197 : ℕ)^5647*10000000000000^4623 ≤ 980013731791^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1493335197 10000000000 980013731791 10000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1043348/1953125 : ℝ), (2539239099/5000000000 : ℝ), (-1493335197/10000000000 : ℝ)] ![(2905789858603/6250000000000 : ℝ), (43707224924323/100000000000000 : ℝ), (980013731791/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1043348/1953125 : ℝ)|^5647 ≤ (2905789858603/6250000000000 : ℝ)^4623
        have hw : |(1043348/1953125 : ℝ)|=(1043348/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2539239099/5000000000 : ℝ)|^5647 ≤ (43707224924323/100000000000000 : ℝ)^4623
        have hw : |(2539239099/5000000000 : ℝ)|=(2539239099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1493335197/10000000000 : ℝ)|^5647 ≤ (980013731791/10000000000000 : ℝ)^4623
        have hw : |(-1493335197/10000000000 : ℝ)|=(1493335197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_s2_3 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2018959069/5000000000 : ℝ)*x 0 + (677535637/2000000000 : ℝ)*x 1 + (38027099/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2018959069/5000000000 : ℝ)^5647 ≤ (16515469883909/50000000000000 : ℝ)^4623 := by
    have hnat : (2018959069 : ℕ)^5647*50000000000000^4623 ≤ 16515469883909^4623*5000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2018959069 5000000000 16515469883909 50000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (677535637/2000000000 : ℝ)^5647 ≤ (2665476843303/10000000000000 : ℝ)^4623 := by
    have hnat : (677535637 : ℕ)^5647*10000000000000^4623 ≤ 2665476843303^4623*2000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677535637 2000000000 2665476843303 10000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (38027099/80000000 : ℝ)^5647 ≤ (10078572944703/25000000000000 : ℝ)^4623 := by
    have hnat : (38027099 : ℕ)^5647*25000000000000^4623 ≤ 10078572944703^4623*80000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38027099 80000000 10078572944703 25000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2018959069/5000000000 : ℝ), (677535637/2000000000 : ℝ), (38027099/80000000 : ℝ)] ![(16515469883909/50000000000000 : ℝ), (2665476843303/10000000000000 : ℝ), (10078572944703/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2018959069/5000000000 : ℝ)|^5647 ≤ (16515469883909/50000000000000 : ℝ)^4623
        have hw : |(2018959069/5000000000 : ℝ)|=(2018959069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(677535637/2000000000 : ℝ)|^5647 ≤ (2665476843303/10000000000000 : ℝ)^4623
        have hw : |(677535637/2000000000 : ℝ)|=(677535637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(38027099/80000000 : ℝ)|^5647 ≤ (10078572944703/25000000000000 : ℝ)^4623
        have hw : |(38027099/80000000 : ℝ)|=(38027099/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_s2_4 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-31715159/250000000 : ℝ)*x 0 + (993238/1953125 : ℝ)*x 1 + (5501106231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31715159/250000000 : ℝ)^5647 ≤ (4014973903431/50000000000000 : ℝ)^4623 := by
    have hnat : (31715159 : ℕ)^5647*50000000000000^4623 ≤ 4014973903431^4623*250000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31715159 250000000 4014973903431 50000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (993238/1953125 : ℝ)^5647 ≤ (43779777149253/100000000000000 : ℝ)^4623 := by
    have hnat : (993238 : ℕ)^5647*100000000000000^4623 ≤ 43779777149253^4623*1953125^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      993238 1953125 43779777149253 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5501106231/10000000000 : ℝ)^5647 ≤ (48190275023403/100000000000000 : ℝ)^4623 := by
    have hnat : (5501106231 : ℕ)^5647*100000000000000^4623 ≤ 48190275023403^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501106231 10000000000 48190275023403 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-31715159/250000000 : ℝ), (993238/1953125 : ℝ), (5501106231/10000000000 : ℝ)] ![(4014973903431/50000000000000 : ℝ), (43779777149253/100000000000000 : ℝ), (48190275023403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-31715159/250000000 : ℝ)|^5647 ≤ (4014973903431/50000000000000 : ℝ)^4623
        have hw : |(-31715159/250000000 : ℝ)|=(31715159/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(993238/1953125 : ℝ)|^5647 ≤ (43779777149253/100000000000000 : ℝ)^4623
        have hw : |(993238/1953125 : ℝ)|=(993238/1953125 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5501106231/10000000000 : ℝ)|^5647 ≤ (48190275023403/100000000000000 : ℝ)^4623
        have hw : |(5501106231/10000000000 : ℝ)|=(5501106231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_s2_5 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (65347771/125000000 : ℝ)*x 0 + (-1070707677/10000000000 : ℝ)*x 1 + (2750553117/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65347771/125000000 : ℝ)^5647 ≤ (22641150117949/50000000000000 : ℝ)^4623 := by
    have hnat : (65347771 : ℕ)^5647*50000000000000^4623 ≤ 22641150117949^4623*125000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65347771 125000000 22641150117949 50000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1070707677/10000000000 : ℝ)^5647 ≤ (652742469521/10000000000000 : ℝ)^4623 := by
    have hnat : (1070707677 : ℕ)^5647*10000000000000^4623 ≤ 652742469521^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070707677 10000000000 652742469521 10000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2750553117/5000000000 : ℝ)^5647 ≤ (3011892190969/6250000000000 : ℝ)^4623 := by
    have hnat : (2750553117 : ℕ)^5647*6250000000000^4623 ≤ 3011892190969^4623*5000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2750553117 5000000000 3011892190969 6250000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65347771/125000000 : ℝ), (-1070707677/10000000000 : ℝ), (2750553117/5000000000 : ℝ)] ![(22641150117949/50000000000000 : ℝ), (652742469521/10000000000000 : ℝ), (3011892190969/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65347771/125000000 : ℝ)|^5647 ≤ (22641150117949/50000000000000 : ℝ)^4623
        have hw : |(65347771/125000000 : ℝ)|=(65347771/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1070707677/10000000000 : ℝ)|^5647 ≤ (652742469521/10000000000000 : ℝ)^4623
        have hw : |(-1070707677/10000000000 : ℝ)|=(1070707677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2750553117/5000000000 : ℝ)|^5647 ≤ (3011892190969/6250000000000 : ℝ)^4623
        have hw : |(2750553117/5000000000 : ℝ)|=(2750553117/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_s2_6 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2613910841/5000000000 : ℝ)*x 0 + (5501106233/10000000000 : ℝ)*x 1 + (-42828307/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2613910841/5000000000 : ℝ)^5647 ≤ (45282300257059/100000000000000 : ℝ)^4623 := by
    have hnat : (2613910841 : ℕ)^5647*100000000000000^4623 ≤ 45282300257059^4623*5000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2613910841 5000000000 45282300257059 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5501106233/10000000000 : ℝ)^5647 ≤ (12047568761201/25000000000000 : ℝ)^4623 := by
    have hnat : (5501106233 : ℕ)^5647*25000000000000^4623 ≤ 12047568761201^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5501106233 10000000000 12047568761201 25000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42828307/400000000 : ℝ)^5647 ≤ (6527424680317/100000000000000 : ℝ)^4623 := by
    have hnat : (42828307 : ℕ)^5647*100000000000000^4623 ≤ 6527424680317^4623*400000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42828307 400000000 6527424680317 100000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2613910841/5000000000 : ℝ), (5501106233/10000000000 : ℝ), (-42828307/400000000 : ℝ)] ![(45282300257059/100000000000000 : ℝ), (12047568761201/25000000000000 : ℝ), (6527424680317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2613910841/5000000000 : ℝ)|^5647 ≤ (45282300257059/100000000000000 : ℝ)^4623
        have hw : |(2613910841/5000000000 : ℝ)|=(2613910841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5501106233/10000000000 : ℝ)|^5647 ≤ (12047568761201/25000000000000 : ℝ)^4623
        have hw : |(5501106233/10000000000 : ℝ)|=(5501106233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-42828307/400000000 : ℝ)|^5647 ≤ (6527424680317/100000000000000 : ℝ)^4623
        have hw : |(-42828307/400000000 : ℝ)|=(42828307/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1742_s2_7 (p : ℝ) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4039089783/10000000000 : ℝ)*x 0 + (4731455469/10000000000 : ℝ)*x 1 + (136402889/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4039089783/10000000000 : ℝ)^5647 ≤ (16521323676317/50000000000000 : ℝ)^4623 := by
    have hnat : (4039089783 : ℕ)^5647*50000000000000^4623 ≤ 16521323676317^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4039089783 10000000000 16521323676317 50000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4731455469/10000000000 : ℝ)^5647 ≤ (20043599362687/50000000000000 : ℝ)^4623 := by
    have hnat : (4731455469 : ℕ)^5647*50000000000000^4623 ≤ 20043599362687^4623*10000000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4731455469 10000000000 20043599362687 50000000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136402889/400000000 : ℝ)^5647 ≤ (3358769237857/12500000000000 : ℝ)^4623 := by
    have hnat : (136402889 : ℕ)^5647*12500000000000^4623 ≤ 3358769237857^4623*400000000^5647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136402889 400000000 3358769237857 12500000000000 5647 4623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5647/1024 : ℝ)) 5647 4623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4039089783/10000000000 : ℝ), (4731455469/10000000000 : ℝ), (136402889/400000000 : ℝ)] ![(16521323676317/50000000000000 : ℝ), (20043599362687/50000000000000 : ℝ), (3358769237857/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4039089783/10000000000 : ℝ)|^5647 ≤ (16521323676317/50000000000000 : ℝ)^4623
        have hw : |(4039089783/10000000000 : ℝ)|=(4039089783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4731455469/10000000000 : ℝ)|^5647 ≤ (20043599362687/50000000000000 : ℝ)^4623
        have hw : |(4731455469/10000000000 : ℝ)|=(4731455469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(136402889/400000000 : ℝ)|^5647 ≤ (3358769237857/12500000000000 : ℝ)^4623
        have hw : |(136402889/400000000 : ℝ)|=(136402889/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1742_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (104462069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18233/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8847/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (279/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9067/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18233/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8847/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18233/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8847/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18233/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8847/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18233/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8847/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18233/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8847/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18233/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8847/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8847/100000 : ℝ) ^ (5631/1024 : ℝ) ≤ (80793546791359/50000000000000000000 : ℝ) := by
    have hpowers : (8847/100000 : ℝ)^5631 ≤ (80793546791359/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8847 : ℕ)^5631*50000000000000000000^1024 ≤ 80793546791359^1024*100000^5631 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8847 100000 80793546791359 50000000000000000000 5631 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8847/100000 : ℝ)) (X := (80793546791359/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5631 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18233/100000 : ℝ) ^ (5631/1024 : ℝ) ≤ (8618695634712617/100000000000000000000 : ℝ) := by
    have hpowers : (18233/100000 : ℝ)^5631 ≤ (8618695634712617/100000000000000000000 : ℝ)^1024 := by
      have hnat : (18233 : ℕ)^5631*100000000000000000000^1024 ≤ 8618695634712617^1024*100000^5631 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18233 100000 8618695634712617 100000000000000000000 5631 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18233/100000 : ℝ)) (X := (8618695634712617/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5631 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000080793546791359/25000000000000000000 : ℝ) ≤ (5000002938465017/5000000000000000 : ℝ) ^ (5631/1024 : ℝ) := by
    have hpowers : (25000080793546791359/25000000000000000000 : ℝ)^1024 ≤ (5000002938465017/5000000000000000 : ℝ)^5631 := by
      have hnat : (25000080793546791359 : ℕ)^1024*5000000000000000^5631 ≤ 5000002938465017^5631*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000080793546791359 25000000000000000000 5000002938465017 5000000000000000 1024 5631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000002938465017/5000000000000000 : ℝ)) (X := (25000080793546791359/25000000000000000000 : ℝ)) (by norm_num) 5631 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20001756056545659067/20000000000000000000 : ℝ) ≤ (10000159664119919/10000000000000000 : ℝ) ^ (5631/1024 : ℝ) := by
    have hpowers : (20001756056545659067/20000000000000000000 : ℝ)^1024 ≤ (10000159664119919/10000000000000000 : ℝ)^5631 := by
      have hnat : (20001756056545659067 : ℕ)^1024*10000000000000000^5631 ≤ 10000159664119919^5631*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20001756056545659067 20000000000000000000 10000159664119919 10000000000000000 1024 5631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000159664119919/10000000000000000 : ℝ)) (X := (20001756056545659067/20000000000000000000 : ℝ)) (by norm_num) 5631 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50008618695634712617/50000000000000000000 : ℝ) ≤ (2500078362827451/2500000000000000 : ℝ) ^ (5631/1024 : ℝ) := by
    have hpowers : (50008618695634712617/50000000000000000000 : ℝ)^1024 ≤ (2500078362827451/2500000000000000 : ℝ)^5631 := by
      have hnat : (50008618695634712617 : ℕ)^1024*2500000000000000^5631 ≤ 2500078362827451^5631*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008618695634712617 50000000000000000000 2500078362827451 2500000000000000 1024 5631 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500078362827451/2500000000000000 : ℝ)) (X := (50008618695634712617/50000000000000000000 : ℝ)) (by norm_num) 5631 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(80793546791359/50000000000000000000 : ℝ) ≤ ((46928667025163736967/46930000000000000000 : ℝ)+2*(30757437977/187720000000000 : ℝ)*(8847/100000 : ℝ))^(5631/1024 : ℝ) := by
    rw [show (46928667025163736967/46930000000000000000 : ℝ)+2*(30757437977/187720000000000 : ℝ)*(8847/100000 : ℝ)=(5000002938465017/5000000000000000 : ℝ) by norm_num, show 1+2*(80793546791359/50000000000000000000 : ℝ)=(25000080793546791359/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8618695634712617/100000000000000000000 : ℝ)+(80793546791359/50000000000000000000 : ℝ) ≤ ((46928667025163736967/46930000000000000000 : ℝ)+(30757437977/187720000000000 : ℝ)*((18233/100000 : ℝ)+(8847/100000 : ℝ)))^(5631/1024 : ℝ) := by
    rw [show (46928667025163736967/46930000000000000000 : ℝ)+(30757437977/187720000000000 : ℝ)*((18233/100000 : ℝ)+(8847/100000 : ℝ))=(10000159664119919/10000000000000000 : ℝ) by norm_num, show 1+(8618695634712617/100000000000000000000 : ℝ)+(80793546791359/50000000000000000000 : ℝ)=(20001756056545659067/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8618695634712617/100000000000000000000 : ℝ) ≤ ((46928667025163736967/46930000000000000000 : ℝ)+2*(30757437977/187720000000000 : ℝ)*(18233/100000 : ℝ))^(5631/1024 : ℝ) := by
    rw [show (46928667025163736967/46930000000000000000 : ℝ)+2*(30757437977/187720000000000 : ℝ)*(18233/100000 : ℝ)=(2500078362827451/2500000000000000 : ℝ) by norm_num, show 1+2*(8618695634712617/100000000000000000000 : ℝ)=(50008618695634712617/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (46928667025163736967/46930000000000000000 : ℝ)*(X 1 0+X 2 0)+(30757437977/187720000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5631/1024 : ℝ)) (lo := (8847/100000 : ℝ)) (hi := (18233/100000 : ℝ)) (c := (46928667025163736967/46930000000000000000 : ℝ)) (alpha := (30757437977/187720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (46928667025163736967/46930000000000000000 : ℝ)*(X 0 1+X 2 1)+(30757437977/187720000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5631/1024 : ℝ)) (lo := (8847/100000 : ℝ)) (hi := (18233/100000 : ℝ)) (c := (46928667025163736967/46930000000000000000 : ℝ)) (alpha := (30757437977/187720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (46928667025163736967/46930000000000000000 : ℝ)*(X 0 2+X 1 2)+(30757437977/187720000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5631/1024 : ℝ)) (lo := (8847/100000 : ℝ)) (hi := (18233/100000 : ℝ)) (c := (46928667025163736967/46930000000000000000 : ℝ)) (alpha := (30757437977/187720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-15852971/125000000 : ℝ)*X 0 0+(2754075641/5000000000 : ℝ)*X 0 1+(5078478823/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5341940713/10000000000 : ℝ)*X 1 0+(-93333479/625000000 : ℝ)*X 1 1+(2539239451/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1043348/1953125 : ℝ)*X 2 0+(2539239099/5000000000 : ℝ)*X 2 1+(-1493335197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2018959069/5000000000 : ℝ)*X 0 0+(677535637/2000000000 : ℝ)*X 0 1+(38027099/80000000 : ℝ)*X 0 2+(2018959069/5000000000 : ℝ)*X 1 0+(677535637/2000000000 : ℝ)*X 1 1+(38027099/80000000 : ℝ)*X 1 2+(2018959069/5000000000 : ℝ)*X 2 0+(677535637/2000000000 : ℝ)*X 2 1+(38027099/80000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-31715159/250000000 : ℝ)*X 0 0+(993238/1953125 : ℝ)*X 0 1+(5501106231/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((65347771/125000000 : ℝ)*X 1 0+(-1070707677/10000000000 : ℝ)*X 1 1+(2750553117/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2613910841/5000000000 : ℝ)*X 2 0+(5501106233/10000000000 : ℝ)*X 2 1+(-42828307/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4039089783/10000000000 : ℝ)*X 0 0+(4731455469/10000000000 : ℝ)*X 0 1+(136402889/400000000 : ℝ)*X 0 2+(4039089783/10000000000 : ℝ)*X 1 0+(4731455469/10000000000 : ℝ)*X 1 1+(136402889/400000000 : ℝ)*X 1 2+(4039089783/10000000000 : ℝ)*X 2 0+(4731455469/10000000000 : ℝ)*X 2 1+(136402889/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1742_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1907059285956136442174591079/180500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1263514621/100000000000000 : ℝ)*(base19) + (402160189/25000000000000 : ℝ)*(base23) + (29655731/50000000000000 : ℝ)*(lower2) + (131877353/100000000000000 : ℝ)*(upper3) + (341597721/100000000000000 : ℝ)*(upper5) + (1529800641580091/100000000000000 : ℝ)*(major0) + (1529800641580091/100000000000000 : ℝ)*(major1) + (1529800641580091/100000000000000 : ℝ)*(major2) + (2327361092005243/100000000000000 : ℝ)*(sp0) + (2327371856822699/100000000000000 : ℝ)*(sp1) + (581842877924141/25000000000000 : ℝ)*(sp2) + (45764011264777/6250000000000 : ℝ)*(sp3) + (12028332077/100000000000000 : ℝ)*(sp4) + (3630405577/100000000000000 : ℝ)*(sp7) + (73222781064201/10000000000000 : ℝ)*(f.failure) + (58184328008433/2500000000000 : ℝ)*(f.sum) + (11010468623673/1877200000000000000000000000 : ℝ)*base65 + (11352381031117673997/4693000000000000000000000000000000 : ℝ)*base67 + (19975494356671673997/4693000000000000000000000000000000 : ℝ)*base69 + (25048241624922673997/4693000000000000000000000000000000 : ℝ)*base71 + (3196541304867/1877200000000000000000000000 : ℝ)*base74 + (5315239453325673997/4693000000000000000000000000000000 : ℝ)*base75 + (20029227113593673997/4693000000000000000000000000000000 : ℝ)*base77 + (29428545106099673997/4693000000000000000000000000000000 : ℝ)*base79 + (5965072624029/1877200000000000000000000000 : ℝ)*base81 + (3291869/500000000000000000000 : ℝ)*base89 + (3291869/500000000000000000000 : ℝ)*base91 + (3291869/500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7664056674248262617904154179/1173250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (216217973/25000000000000 : ℝ)*(base19) + (928890937/100000000000000 : ℝ)*(base23) + (143035007/100000000000000 : ℝ)*(upper3) + (13896757/50000000000000 : ℝ)*(lower4) + (4277831/3125000000000 : ℝ)*(upper5) + (790550837293079/50000000000000 : ℝ)*(major0) + (790550837293079/50000000000000 : ℝ)*(major1) + (790550837293079/50000000000000 : ℝ)*(major2) + (5839264927/100000000000000 : ℝ)*(sp1) + (1573573753/25000000000000 : ℝ)*(sp2) + (1202710229575943/50000000000000 : ℝ)*(sp4) + (1202706877507533/50000000000000 : ℝ)*(sp5) + (2405413235965937/100000000000000 : ℝ)*(sp6) + (756782672276077/100000000000000 : ℝ)*(sp7) + (756782672276077/100000000000000 : ℝ)*(f.failure) + (1202710229575943/50000000000000 : ℝ)*(f.sum) + (36640865449/23465000000000000000000000 : ℝ)*base65 + (18647689844553198607/2346500000000000000000000000000000 : ℝ)*base68 + (10241315388840198607/2346500000000000000000000000000000 : ℝ)*base70 + (3697218120768301393/2346500000000000000000000000000000 : ℝ)*base71 + (5874766801149/1173250000000000000000000000 : ℝ)*base74 + (7956754335721801393/2346500000000000000000000000000000 : ℝ)*base75 + (5052512736651198607/2346500000000000000000000000000000 : ℝ)*base78 + (16724896263123698607/2346500000000000000000000000000000 : ℝ)*base80 + (2310945584123/938600000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (42623313/5000000000000000000000 : ℝ)*base89 + (42623313/5000000000000000000000 : ℝ)*base91 + (42623313/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1742_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (104462069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18233/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8847/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (279/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9067/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1742_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1742_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (104462069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (279/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9067/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1742_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1742_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1742_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5631/1024 : ℝ) ≤ p) (hpb : p ≤ (5647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (104462069/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (279/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9067/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1742_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
