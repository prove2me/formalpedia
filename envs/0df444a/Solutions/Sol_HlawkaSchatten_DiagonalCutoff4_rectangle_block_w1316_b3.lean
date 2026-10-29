-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1316_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:42:14.303238+00:00
-- url     : https://prove2.me/submissions/a263dabb-2f5a-409c-b5e9-d84b1c4a378d

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
theorem support_rectangle_w1316_box_0 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-29645301/156250000 : ℝ)*x 0 + (168469443/312500000 : ℝ)*x 1 + (5391021793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (29645301/156250000 : ℝ)^1069 ≤ (5620862768903/50000000000000 : ℝ)^813 := by
    have hnat : (29645301 : ℕ)^1069*50000000000000^813 ≤ 5620862768903^813*156250000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29645301 156250000 5620862768903 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168469443/312500000 : ℝ)^1069 ≤ (22189569647521/50000000000000 : ℝ)^813 := by
    have hnat : (168469443 : ℕ)^1069*50000000000000^813 ≤ 22189569647521^813*312500000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168469443 312500000 22189569647521 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391021793/10000000000 : ℝ)^1069 ≤ (22189567574691/50000000000000 : ℝ)^813 := by
    have hnat : (5391021793 : ℕ)^1069*50000000000000^813 ≤ 22189567574691^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391021793 10000000000 22189567574691 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-29645301/156250000 : ℝ), (168469443/312500000 : ℝ), (5391021793/10000000000 : ℝ)] ![(5620862768903/50000000000000 : ℝ), (22189569647521/50000000000000 : ℝ), (22189567574691/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-29645301/156250000 : ℝ)|^1069 ≤ (5620862768903/50000000000000 : ℝ)^813
        have hw : |(-29645301/156250000 : ℝ)|=(29645301/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168469443/312500000 : ℝ)|^1069 ≤ (22189569647521/50000000000000 : ℝ)^813
        have hw : |(168469443/312500000 : ℝ)|=(168469443/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391021793/10000000000 : ℝ)|^1069 ≤ (22189567574691/50000000000000 : ℝ)^813
        have hw : |(5391021793/10000000000 : ℝ)|=(5391021793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_box_1 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5284778503/10000000000 : ℝ)*x 0 + (-510680529/2500000000 : ℝ)*x 1 + (2695511343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284778503/10000000000 : ℝ)^1069 ≤ (10808180821651/25000000000000 : ℝ)^813 := by
    have hnat : (5284778503 : ℕ)^1069*25000000000000^813 ≤ 10808180821651^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284778503 10000000000 10808180821651 25000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (510680529/2500000000 : ℝ)^1069 ≤ (6194065944761/50000000000000 : ℝ)^813 := by
    have hnat : (510680529 : ℕ)^1069*50000000000000^813 ≤ 6194065944761^813*2500000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510680529 2500000000 6194065944761 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695511343/5000000000 : ℝ)^1069 ≤ (11094786203843/25000000000000 : ℝ)^813 := by
    have hnat : (2695511343 : ℕ)^1069*25000000000000^813 ≤ 11094786203843^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695511343 5000000000 11094786203843 25000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284778503/10000000000 : ℝ), (-510680529/2500000000 : ℝ), (2695511343/5000000000 : ℝ)] ![(10808180821651/25000000000000 : ℝ), (6194065944761/50000000000000 : ℝ), (11094786203843/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284778503/10000000000 : ℝ)|^1069 ≤ (10808180821651/25000000000000 : ℝ)^813
        have hw : |(5284778503/10000000000 : ℝ)|=(5284778503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-510680529/2500000000 : ℝ)|^1069 ≤ (6194065944761/50000000000000 : ℝ)^813
        have hw : |(-510680529/2500000000 : ℝ)|=(510680529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695511343/5000000000 : ℝ)|^1069 ≤ (11094786203843/25000000000000 : ℝ)^813
        have hw : |(2695511343/5000000000 : ℝ)|=(2695511343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_box_2 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2642389507/5000000000 : ℝ)*x 0 + (2695511141/5000000000 : ℝ)*x 1 + (-81708879/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642389507/5000000000 : ℝ)^1069 ≤ (43232728783201/100000000000000 : ℝ)^813 := by
    have hnat : (2642389507 : ℕ)^1069*100000000000000^813 ≤ 43232728783201^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642389507 5000000000 43232728783201 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695511141/5000000000 : ℝ)^1069 ≤ (11094785110601/25000000000000 : ℝ)^813 := by
    have hnat : (2695511141 : ℕ)^1069*25000000000000^813 ≤ 11094785110601^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695511141 5000000000 11094785110601 25000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81708879/400000000 : ℝ)^1069 ≤ (12388130765169/100000000000000 : ℝ)^813 := by
    have hnat : (81708879 : ℕ)^1069*100000000000000^813 ≤ 12388130765169^813*400000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81708879 400000000 12388130765169 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642389507/5000000000 : ℝ), (2695511141/5000000000 : ℝ), (-81708879/400000000 : ℝ)] ![(43232728783201/100000000000000 : ℝ), (11094785110601/25000000000000 : ℝ), (12388130765169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642389507/5000000000 : ℝ)|^1069 ≤ (43232728783201/100000000000000 : ℝ)^813
        have hw : |(2642389507/5000000000 : ℝ)|=(2642389507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695511141/5000000000 : ℝ)|^1069 ≤ (11094785110601/25000000000000 : ℝ)^813
        have hw : |(2695511141/5000000000 : ℝ)|=(2695511141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-81708879/400000000 : ℝ)|^1069 ≤ (12388130765169/100000000000000 : ℝ)^813
        have hw : |(-81708879/400000000 : ℝ)|=(81708879/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_box_3 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4482282367/10000000000 : ℝ)*x 0 + (852601527/2000000000 : ℝ)*x 1 + (5328759/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4482282367/10000000000 : ℝ)^1069 ≤ (34814662266589/100000000000000 : ℝ)^813 := by
    have hnat : (4482282367 : ℕ)^1069*100000000000000^813 ≤ 34814662266589^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482282367 10000000000 34814662266589 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (852601527/2000000000 : ℝ)^1069 ≤ (16296335522579/50000000000000 : ℝ)^813 := by
    have hnat : (852601527 : ℕ)^1069*50000000000000^813 ≤ 16296335522579^813*2000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      852601527 2000000000 16296335522579 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5328759/12500000 : ℝ)^1069 ≤ (651853333443/2000000000000 : ℝ)^813 := by
    have hnat : (5328759 : ℕ)^1069*2000000000000^813 ≤ 651853333443^813*12500000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5328759 12500000 651853333443 2000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4482282367/10000000000 : ℝ), (852601527/2000000000 : ℝ), (5328759/12500000 : ℝ)] ![(34814662266589/100000000000000 : ℝ), (16296335522579/50000000000000 : ℝ), (651853333443/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4482282367/10000000000 : ℝ)|^1069 ≤ (34814662266589/100000000000000 : ℝ)^813
        have hw : |(4482282367/10000000000 : ℝ)|=(4482282367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(852601527/2000000000 : ℝ)|^1069 ≤ (16296335522579/50000000000000 : ℝ)^813
        have hw : |(852601527/2000000000 : ℝ)|=(852601527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5328759/12500000 : ℝ)|^1069 ≤ (651853333443/2000000000000 : ℝ)^813
        have hw : |(5328759/12500000 : ℝ)|=(5328759/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_box_4 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-559689211/2500000000 : ℝ)*x 0 + (1316079389/2500000000 : ℝ)*x 1 + (2632158889/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (559689211/2500000000 : ℝ)^1069 ≤ (6987230416953/50000000000000 : ℝ)^813 := by
    have hnat : (559689211 : ℕ)^1069*50000000000000^813 ≤ 6987230416953^813*2500000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559689211 2500000000 6987230416953 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316079389/2500000000 : ℝ)^1069 ≤ (10753192095751/25000000000000 : ℝ)^813 := by
    have hnat : (1316079389 : ℕ)^1069*25000000000000^813 ≤ 10753192095751^813*2500000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316079389 2500000000 10753192095751 25000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632158889/5000000000 : ℝ)^1069 ≤ (43012770768043/100000000000000 : ℝ)^813 := by
    have hnat : (2632158889 : ℕ)^1069*100000000000000^813 ≤ 43012770768043^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632158889 5000000000 43012770768043 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-559689211/2500000000 : ℝ), (1316079389/2500000000 : ℝ), (2632158889/5000000000 : ℝ)] ![(6987230416953/50000000000000 : ℝ), (10753192095751/25000000000000 : ℝ), (43012770768043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-559689211/2500000000 : ℝ)|^1069 ≤ (6987230416953/50000000000000 : ℝ)^813
        have hw : |(-559689211/2500000000 : ℝ)|=(559689211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316079389/2500000000 : ℝ)|^1069 ≤ (10753192095751/25000000000000 : ℝ)^813
        have hw : |(1316079389/2500000000 : ℝ)|=(1316079389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632158889/5000000000 : ℝ)|^1069 ≤ (43012770768043/100000000000000 : ℝ)^813
        have hw : |(2632158889/5000000000 : ℝ)|=(2632158889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_box_5 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (134346807/250000000 : ℝ)*x 0 + (-83735087/400000000 : ℝ)*x 1 + (5264317773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134346807/250000000 : ℝ)^1069 ≤ (22096799407283/50000000000000 : ℝ)^813 := by
    have hnat : (134346807 : ℕ)^1069*50000000000000^813 ≤ 22096799407283^813*250000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134346807 250000000 22096799407283 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (83735087/400000000 : ℝ)^1069 ≤ (1279363045569/10000000000000 : ℝ)^813 := by
    have hnat : (83735087 : ℕ)^1069*10000000000000^813 ≤ 1279363045569^813*400000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83735087 400000000 1279363045569 10000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264317773/10000000000 : ℝ)^1069 ≤ (21506385357163/50000000000000 : ℝ)^813 := by
    have hnat : (5264317773 : ℕ)^1069*50000000000000^813 ≤ 21506385357163^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264317773 10000000000 21506385357163 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134346807/250000000 : ℝ), (-83735087/400000000 : ℝ), (5264317773/10000000000 : ℝ)] ![(22096799407283/50000000000000 : ℝ), (1279363045569/10000000000000 : ℝ), (21506385357163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134346807/250000000 : ℝ)|^1069 ≤ (22096799407283/50000000000000 : ℝ)^813
        have hw : |(134346807/250000000 : ℝ)|=(134346807/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-83735087/400000000 : ℝ)|^1069 ≤ (1279363045569/10000000000000 : ℝ)^813
        have hw : |(-83735087/400000000 : ℝ)|=(83735087/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264317773/10000000000 : ℝ)|^1069 ≤ (21506385357163/50000000000000 : ℝ)^813
        have hw : |(5264317773/10000000000 : ℝ)|=(5264317773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_box_6 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5373872343/10000000000 : ℝ)*x 0 + (1052863519/2000000000 : ℝ)*x 1 + (-130836083/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373872343/10000000000 : ℝ)^1069 ≤ (8838719899161/20000000000000 : ℝ)^813 := by
    have hnat : (5373872343 : ℕ)^1069*20000000000000^813 ≤ 8838719899161^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373872343 10000000000 8838719899161 20000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052863519/2000000000 : ℝ)^1069 ≤ (43012768801997/100000000000000 : ℝ)^813 := by
    have hnat : (1052863519 : ℕ)^1069*100000000000000^813 ≤ 43012768801997^813*2000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052863519 2000000000 43012768801997 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130836083/625000000 : ℝ)^1069 ≤ (12793631685179/100000000000000 : ℝ)^813 := by
    have hnat : (130836083 : ℕ)^1069*100000000000000^813 ≤ 12793631685179^813*625000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130836083 625000000 12793631685179 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373872343/10000000000 : ℝ), (1052863519/2000000000 : ℝ), (-130836083/625000000 : ℝ)] ![(8838719899161/20000000000000 : ℝ), (43012768801997/100000000000000 : ℝ), (12793631685179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373872343/10000000000 : ℝ)|^1069 ≤ (8838719899161/20000000000000 : ℝ)^813
        have hw : |(5373872343/10000000000 : ℝ)|=(5373872343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052863519/2000000000 : ℝ)|^1069 ≤ (43012768801997/100000000000000 : ℝ)^813
        have hw : |(1052863519/2000000000 : ℝ)|=(1052863519/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-130836083/625000000 : ℝ)|^1069 ≤ (12793631685179/100000000000000 : ℝ)^813
        have hw : |(-130836083/625000000 : ℝ)|=(130836083/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_box_7 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4183764363/10000000000 : ℝ)*x 0 + (2206105979/5000000000 : ℝ)*x 1 + (4412211897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4183764363/10000000000 : ℝ)^1069 ≤ (15899194202117/50000000000000 : ℝ)^813 := by
    have hnat : (4183764363 : ℕ)^1069*50000000000000^813 ≤ 15899194202117^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4183764363 10000000000 15899194202117 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2206105979/5000000000 : ℝ)^1069 ≤ (3410080610423/10000000000000 : ℝ)^813 := by
    have hnat : (2206105979 : ℕ)^1069*10000000000000^813 ≤ 3410080610423^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2206105979 5000000000 3410080610423 10000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4412211897/10000000000 : ℝ)^1069 ≤ (1364032219373/4000000000000 : ℝ)^813 := by
    have hnat : (4412211897 : ℕ)^1069*4000000000000^813 ≤ 1364032219373^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4412211897 10000000000 1364032219373 4000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4183764363/10000000000 : ℝ), (2206105979/5000000000 : ℝ), (4412211897/10000000000 : ℝ)] ![(15899194202117/50000000000000 : ℝ), (3410080610423/10000000000000 : ℝ), (1364032219373/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4183764363/10000000000 : ℝ)|^1069 ≤ (15899194202117/50000000000000 : ℝ)^813
        have hw : |(4183764363/10000000000 : ℝ)|=(4183764363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2206105979/5000000000 : ℝ)|^1069 ≤ (3410080610423/10000000000000 : ℝ)^813
        have hw : |(2206105979/5000000000 : ℝ)|=(2206105979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4412211897/10000000000 : ℝ)|^1069 ≤ (1364032219373/4000000000000 : ℝ)^813
        have hw : |(4412211897/10000000000 : ℝ)|=(4412211897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_box_8 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2167122523/10000000000 : ℝ)*x 0 + (5177215337/10000000000 : ℝ)*x 1 + (2702525879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2167122523/10000000000 : ℝ)^1069 ≤ (6694750011271/50000000000000 : ℝ)^813 := by
    have hnat : (2167122523 : ℕ)^1069*50000000000000^813 ≤ 6694750011271^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2167122523 10000000000 6694750011271 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177215337/10000000000 : ℝ)^1069 ≤ (84158879589/200000000000 : ℝ)^813 := by
    have hnat : (5177215337 : ℕ)^1069*200000000000^813 ≤ 84158879589^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177215337 10000000000 84158879589 200000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2702525879/5000000000 : ℝ)^1069 ≤ (11132765042039/25000000000000 : ℝ)^813 := by
    have hnat : (2702525879 : ℕ)^1069*25000000000000^813 ≤ 11132765042039^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702525879 5000000000 11132765042039 25000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2167122523/10000000000 : ℝ), (5177215337/10000000000 : ℝ), (2702525879/5000000000 : ℝ)] ![(6694750011271/50000000000000 : ℝ), (84158879589/200000000000 : ℝ), (11132765042039/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2167122523/10000000000 : ℝ)|^1069 ≤ (6694750011271/50000000000000 : ℝ)^813
        have hw : |(-2167122523/10000000000 : ℝ)|=(2167122523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177215337/10000000000 : ℝ)|^1069 ≤ (84158879589/200000000000 : ℝ)^813
        have hw : |(5177215337/10000000000 : ℝ)|=(5177215337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2702525879/5000000000 : ℝ)|^1069 ≤ (11132765042039/25000000000000 : ℝ)^813
        have hw : |(2702525879/5000000000 : ℝ)|=(2702525879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_box_9 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5274908163/10000000000 : ℝ)*x 0 + (-509244669/2500000000 : ℝ)*x 1 + (216202081/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274908163/10000000000 : ℝ)^1069 ≤ (8625316744619/20000000000000 : ℝ)^813 := by
    have hnat : (5274908163 : ℕ)^1069*20000000000000^813 ≤ 8625316744619^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274908163 10000000000 8625316744619 20000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (509244669/2500000000 : ℝ)^1069 ≤ (3085588299867/25000000000000 : ℝ)^813 := by
    have hnat : (509244669 : ℕ)^1069*25000000000000^813 ≤ 3085588299867^813*2500000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509244669 2500000000 3085588299867 25000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216202081/400000000 : ℝ)^1069 ≤ (44531063060577/100000000000000 : ℝ)^813 := by
    have hnat : (216202081 : ℕ)^1069*100000000000000^813 ≤ 44531063060577^813*400000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216202081 400000000 44531063060577 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274908163/10000000000 : ℝ), (-509244669/2500000000 : ℝ), (216202081/400000000 : ℝ)] ![(8625316744619/20000000000000 : ℝ), (3085588299867/25000000000000 : ℝ), (44531063060577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274908163/10000000000 : ℝ)|^1069 ≤ (8625316744619/20000000000000 : ℝ)^813
        have hw : |(5274908163/10000000000 : ℝ)|=(5274908163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-509244669/2500000000 : ℝ)|^1069 ≤ (3085588299867/25000000000000 : ℝ)^813
        have hw : |(-509244669/2500000000 : ℝ)|=(509244669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216202081/400000000 : ℝ)|^1069 ≤ (44531063060577/100000000000000 : ℝ)^813
        have hw : |(216202081/400000000 : ℝ)|=(216202081/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_box_10 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5274908201/10000000000 : ℝ)*x 0 + (5405052083/10000000000 : ℝ)*x 1 + (-407395709/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5274908201/10000000000 : ℝ)^1069 ≤ (43126584131603/100000000000000 : ℝ)^813 := by
    have hnat : (5274908201 : ℕ)^1069*100000000000000^813 ≤ 43126584131603^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274908201 10000000000 43126584131603 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5405052083/10000000000 : ℝ)^1069 ≤ (22265531844447/50000000000000 : ℝ)^813 := by
    have hnat : (5405052083 : ℕ)^1069*50000000000000^813 ≤ 22265531844447^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5405052083 10000000000 22265531844447 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (407395709/2000000000 : ℝ)^1069 ≤ (12342352155781/100000000000000 : ℝ)^813 := by
    have hnat : (407395709 : ℕ)^1069*100000000000000^813 ≤ 12342352155781^813*2000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407395709 2000000000 12342352155781 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5274908201/10000000000 : ℝ), (5405052083/10000000000 : ℝ), (-407395709/2000000000 : ℝ)] ![(43126584131603/100000000000000 : ℝ), (22265531844447/50000000000000 : ℝ), (12342352155781/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5274908201/10000000000 : ℝ)|^1069 ≤ (43126584131603/100000000000000 : ℝ)^813
        have hw : |(5274908201/10000000000 : ℝ)|=(5274908201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5405052083/10000000000 : ℝ)|^1069 ≤ (22265531844447/50000000000000 : ℝ)^813
        have hw : |(5405052083/10000000000 : ℝ)|=(5405052083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-407395709/2000000000 : ℝ)|^1069 ≤ (12342352155781/100000000000000 : ℝ)^813
        have hw : |(-407395709/2000000000 : ℝ)|=(407395709/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_box_11 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2257388641/5000000000 : ℝ)*x 0 + (4246472439/10000000000 : ℝ)*x 1 + (106161809/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2257388641/5000000000 : ℝ)^1069 ≤ (35146908556953/100000000000000 : ℝ)^813 := by
    have hnat : (2257388641 : ℕ)^1069*100000000000000^813 ≤ 35146908556953^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257388641 5000000000 35146908556953 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4246472439/10000000000 : ℝ)^1069 ≤ (32426546112111/100000000000000 : ℝ)^813 := by
    have hnat : (4246472439 : ℕ)^1069*100000000000000^813 ≤ 32426546112111^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4246472439 10000000000 32426546112111 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106161809/250000000 : ℝ)^1069 ≤ (4053318164863/12500000000000 : ℝ)^813 := by
    have hnat : (106161809 : ℕ)^1069*12500000000000^813 ≤ 4053318164863^813*250000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106161809 250000000 4053318164863 12500000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2257388641/5000000000 : ℝ), (4246472439/10000000000 : ℝ), (106161809/250000000 : ℝ)] ![(35146908556953/100000000000000 : ℝ), (32426546112111/100000000000000 : ℝ), (4053318164863/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2257388641/5000000000 : ℝ)|^1069 ≤ (35146908556953/100000000000000 : ℝ)^813
        have hw : |(2257388641/5000000000 : ℝ)|=(2257388641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4246472439/10000000000 : ℝ)|^1069 ≤ (32426546112111/100000000000000 : ℝ)^813
        have hw : |(4246472439/10000000000 : ℝ)|=(4246472439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(106161809/250000000 : ℝ)|^1069 ≤ (4053318164863/12500000000000 : ℝ)^813
        have hw : |(106161809/250000000 : ℝ)|=(106161809/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_box_12 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1969322527/10000000000 : ℝ)*x 0 + (5475858517/10000000000 : ℝ)*x 1 + (2626635869/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1969322527/10000000000 : ℝ)^1069 ≤ (2951543068413/25000000000000 : ℝ)^813 := by
    have hnat : (1969322527 : ℕ)^1069*25000000000000^813 ≤ 2951543068413^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1969322527 10000000000 2951543068413 25000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5475858517/10000000000 : ℝ)^1069 ≤ (11324922485911/25000000000000 : ℝ)^813 := by
    have hnat : (5475858517 : ℕ)^1069*25000000000000^813 ≤ 11324922485911^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475858517 10000000000 11324922485911 25000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626635869/5000000000 : ℝ)^1069 ≤ (21447068881913/50000000000000 : ℝ)^813 := by
    have hnat : (2626635869 : ℕ)^1069*50000000000000^813 ≤ 21447068881913^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626635869 5000000000 21447068881913 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1969322527/10000000000 : ℝ), (5475858517/10000000000 : ℝ), (2626635869/5000000000 : ℝ)] ![(2951543068413/25000000000000 : ℝ), (11324922485911/25000000000000 : ℝ), (21447068881913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1969322527/10000000000 : ℝ)|^1069 ≤ (2951543068413/25000000000000 : ℝ)^813
        have hw : |(-1969322527/10000000000 : ℝ)|=(1969322527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5475858517/10000000000 : ℝ)|^1069 ≤ (11324922485911/25000000000000 : ℝ)^813
        have hw : |(5475858517/10000000000 : ℝ)|=(5475858517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626635869/5000000000 : ℝ)|^1069 ≤ (21447068881913/50000000000000 : ℝ)^813
        have hw : |(2626635869/5000000000 : ℝ)|=(2626635869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_box_13 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1345409187/2500000000 : ℝ)*x 0 + (-2097689097/10000000000 : ℝ)*x 1 + (525327107/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1345409187/2500000000 : ℝ)^1069 ≤ (44277577610227/100000000000000 : ℝ)^813 := by
    have hnat : (1345409187 : ℕ)^1069*100000000000000^813 ≤ 44277577610227^813*2500000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345409187 2500000000 44277577610227 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2097689097/10000000000 : ℝ)^1069 ≤ (6414145888909/50000000000000 : ℝ)^813 := by
    have hnat : (2097689097 : ℕ)^1069*50000000000000^813 ≤ 6414145888909^813*10000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097689097 10000000000 6414145888909 50000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525327107/1000000000 : ℝ)^1069 ≤ (1340441580999/3125000000000 : ℝ)^813 := by
    have hnat : (525327107 : ℕ)^1069*3125000000000^813 ≤ 1340441580999^813*1000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525327107 1000000000 1340441580999 3125000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1345409187/2500000000 : ℝ), (-2097689097/10000000000 : ℝ), (525327107/1000000000 : ℝ)] ![(44277577610227/100000000000000 : ℝ), (6414145888909/50000000000000 : ℝ), (1340441580999/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1345409187/2500000000 : ℝ)|^1069 ≤ (44277577610227/100000000000000 : ℝ)^813
        have hw : |(1345409187/2500000000 : ℝ)|=(1345409187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2097689097/10000000000 : ℝ)|^1069 ≤ (6414145888909/50000000000000 : ℝ)^813
        have hw : |(-2097689097/10000000000 : ℝ)|=(2097689097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(525327107/1000000000 : ℝ)|^1069 ≤ (1340441580999/3125000000000 : ℝ)^813
        have hw : |(525327107/1000000000 : ℝ)|=(525327107/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_box_14 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (134540921/250000000 : ℝ)*x 0 + (525327089/1000000000 : ℝ)*x 1 + (-1048844607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134540921/250000000 : ℝ)^1069 ≤ (8855515721101/20000000000000 : ℝ)^813 := by
    have hnat : (134540921 : ℕ)^1069*20000000000000^813 ≤ 8855515721101^813*250000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134540921 250000000 8855515721101 20000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (525327089/1000000000 : ℝ)^1069 ≤ (42894128659431/100000000000000 : ℝ)^813 := by
    have hnat : (525327089 : ℕ)^1069*100000000000000^813 ≤ 42894128659431^813*1000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525327089 1000000000 42894128659431 100000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048844607/5000000000 : ℝ)^1069 ≤ (102626341749/800000000000 : ℝ)^813 := by
    have hnat : (1048844607 : ℕ)^1069*800000000000^813 ≤ 102626341749^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048844607 5000000000 102626341749 800000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134540921/250000000 : ℝ), (525327089/1000000000 : ℝ), (-1048844607/5000000000 : ℝ)] ![(8855515721101/20000000000000 : ℝ), (42894128659431/100000000000000 : ℝ), (102626341749/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134540921/250000000 : ℝ)|^1069 ≤ (8855515721101/20000000000000 : ℝ)^813
        have hw : |(134540921/250000000 : ℝ)|=(134540921/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(525327089/1000000000 : ℝ)|^1069 ≤ (42894128659431/100000000000000 : ℝ)^813
        have hw : |(525327089/1000000000 : ℝ)|=(525327089/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1048844607/5000000000 : ℝ)|^1069 ≤ (102626341749/800000000000 : ℝ)^813
        have hw : |(-1048844607/5000000000 : ℝ)|=(1048844607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1316_box_15 (p : ℝ) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2078645453/5000000000 : ℝ)*x 0 + (2212604661/5000000000 : ℝ)*x 1 + (553151309/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2078645453/5000000000 : ℝ)^1069 ≤ (7883521333783/25000000000000 : ℝ)^813 := by
    have hnat : (2078645453 : ℕ)^1069*25000000000000^813 ≤ 7883521333783^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2078645453 5000000000 7883521333783 25000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2212604661/5000000000 : ℝ)^1069 ≤ (1069779733629/3125000000000 : ℝ)^813 := by
    have hnat : (2212604661 : ℕ)^1069*3125000000000^813 ≤ 1069779733629^813*5000000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2212604661 5000000000 1069779733629 3125000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (553151309/1250000000 : ℝ)^1069 ≤ (6846592634739/20000000000000 : ℝ)^813 := by
    have hnat : (553151309 : ℕ)^1069*20000000000000^813 ≤ 6846592634739^813*1250000000^1069 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553151309 1250000000 6846592634739 20000000000000 1069 813 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1069/256 : ℝ)) 1069 813 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2078645453/5000000000 : ℝ), (2212604661/5000000000 : ℝ), (553151309/1250000000 : ℝ)] ![(7883521333783/25000000000000 : ℝ), (1069779733629/3125000000000 : ℝ), (6846592634739/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2078645453/5000000000 : ℝ)|^1069 ≤ (7883521333783/25000000000000 : ℝ)^813
        have hw : |(2078645453/5000000000 : ℝ)|=(2078645453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2212604661/5000000000 : ℝ)|^1069 ≤ (1069779733629/3125000000000 : ℝ)^813
        have hw : |(2212604661/5000000000 : ℝ)|=(2212604661/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(553151309/1250000000 : ℝ)|^1069 ≤ (6846592634739/20000000000000 : ℝ)^813
        have hw : |(553151309/1250000000 : ℝ)|=(553151309/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1316_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76852523/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14689/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (693/6250 : ℝ)*pair X i i ≤ pair X i h) :
    -(31423/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58891/100000 : ℝ) ∧ (79801/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (337/400 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14689/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (693/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14689/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (693/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14689/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (693/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14689/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (693/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14689/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (693/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14689/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (693/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (693/6250 : ℝ) ^ (4275/1024 : ℝ) ≤ (2058158087103753/20000000000000000000 : ℝ) := by
    have hpowers : (693/6250 : ℝ)^4275 ≤ (2058158087103753/20000000000000000000 : ℝ)^1024 := by
      have hnat : (693 : ℕ)^4275*20000000000000000000^1024 ≤ 2058158087103753^1024*6250^4275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        693 6250 2058158087103753 20000000000000000000 4275 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (693/6250 : ℝ)) (X := (2058158087103753/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14689/100000 : ℝ) ^ (4275/1024 : ℝ) ≤ (41616473250743/125000000000000000 : ℝ) := by
    have hpowers : (14689/100000 : ℝ)^4275 ≤ (41616473250743/125000000000000000 : ℝ)^1024 := by
      have hnat : (14689 : ℕ)^4275*125000000000000000^1024 ≤ 41616473250743^1024*100000^4275 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14689 100000 41616473250743 125000000000000000 4275 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14689/100000 : ℝ)) (X := (41616473250743/125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002058158087103753/10000000000000000000 : ℝ) ≤ (5000246478241853/5000000000000000 : ℝ) ^ (4275/1024 : ℝ) := by
    have hpowers : (10002058158087103753/10000000000000000000 : ℝ)^1024 ≤ (5000246478241853/5000000000000000 : ℝ)^4275 := by
      have hnat : (10002058158087103753 : ℕ)^1024*5000000000000000^4275 ≤ 5000246478241853^4275*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002058158087103753 10000000000000000000 5000246478241853 5000000000000000 1024 4275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000246478241853/5000000000000000 : ℝ)) (X := (10002058158087103753/10000000000000000000 : ℝ)) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008716793807222633/20000000000000000000 : ℝ) ≤ (5000521901638093/5000000000000000 : ℝ) ^ (4275/1024 : ℝ) := by
    have hpowers : (20008716793807222633/20000000000000000000 : ℝ)^1024 ≤ (5000521901638093/5000000000000000 : ℝ)^4275 := by
      have hnat : (20008716793807222633 : ℕ)^1024*5000000000000000^4275 ≤ 5000521901638093^4275*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008716793807222633 20000000000000000000 5000521901638093 5000000000000000 1024 4275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000521901638093/5000000000000000 : ℝ)) (X := (20008716793807222633/20000000000000000000 : ℝ)) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (62541616473250743/62500000000000000 : ℝ) ≤ (5000797325034333/5000000000000000 : ℝ) ^ (4275/1024 : ℝ) := by
    have hpowers : (62541616473250743/62500000000000000 : ℝ)^1024 ≤ (5000797325034333/5000000000000000 : ℝ)^4275 := by
      have hnat : (62541616473250743 : ℕ)^1024*5000000000000000^4275 ≤ 5000797325034333^4275*62500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62541616473250743 62500000000000000 5000797325034333 5000000000000000 1024 4275 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000797325034333/5000000000000000 : ℝ)) (X := (62541616473250743/62500000000000000 : ℝ)) (by norm_num) 4275 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2058158087103753/20000000000000000000 : ℝ) ≤ ((17999779778913894413/18005000000000000000 : ℝ)+2*(3442792453/2250625000000 : ℝ)*(693/6250 : ℝ))^(4275/1024 : ℝ) := by
    rw [show (17999779778913894413/18005000000000000000 : ℝ)+2*(3442792453/2250625000000 : ℝ)*(693/6250 : ℝ)=(5000246478241853/5000000000000000 : ℝ) by norm_num, show 1+2*(2058158087103753/20000000000000000000 : ℝ)=(10002058158087103753/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(41616473250743/125000000000000000 : ℝ)+(2058158087103753/20000000000000000000 : ℝ) ≤ ((17999779778913894413/18005000000000000000 : ℝ)+(3442792453/2250625000000 : ℝ)*((14689/100000 : ℝ)+(693/6250 : ℝ)))^(4275/1024 : ℝ) := by
    rw [show (17999779778913894413/18005000000000000000 : ℝ)+(3442792453/2250625000000 : ℝ)*((14689/100000 : ℝ)+(693/6250 : ℝ))=(5000521901638093/5000000000000000 : ℝ) by norm_num, show 1+(41616473250743/125000000000000000 : ℝ)+(2058158087103753/20000000000000000000 : ℝ)=(20008716793807222633/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(41616473250743/125000000000000000 : ℝ) ≤ ((17999779778913894413/18005000000000000000 : ℝ)+2*(3442792453/2250625000000 : ℝ)*(14689/100000 : ℝ))^(4275/1024 : ℝ) := by
    rw [show (17999779778913894413/18005000000000000000 : ℝ)+2*(3442792453/2250625000000 : ℝ)*(14689/100000 : ℝ)=(5000797325034333/5000000000000000 : ℝ) by norm_num, show 1+2*(41616473250743/125000000000000000 : ℝ)=(62541616473250743/62500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17999779778913894413/18005000000000000000 : ℝ)*(X 1 0+X 2 0)+(3442792453/2250625000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4275/1024 : ℝ)) (lo := (693/6250 : ℝ)) (hi := (14689/100000 : ℝ)) (c := (17999779778913894413/18005000000000000000 : ℝ)) (alpha := (3442792453/2250625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17999779778913894413/18005000000000000000 : ℝ)*(X 0 1+X 2 1)+(3442792453/2250625000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4275/1024 : ℝ)) (lo := (693/6250 : ℝ)) (hi := (14689/100000 : ℝ)) (c := (17999779778913894413/18005000000000000000 : ℝ)) (alpha := (3442792453/2250625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17999779778913894413/18005000000000000000 : ℝ)*(X 0 2+X 1 2)+(3442792453/2250625000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4275/1024 : ℝ)) (lo := (693/6250 : ℝ)) (hi := (14689/100000 : ℝ)) (c := (17999779778913894413/18005000000000000000 : ℝ)) (alpha := (3442792453/2250625000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-29645301/156250000 : ℝ)*X 0 0+(168469443/312500000 : ℝ)*X 0 1+(5391021793/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5284778503/10000000000 : ℝ)*X 1 0+(-510680529/2500000000 : ℝ)*X 1 1+(2695511343/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2642389507/5000000000 : ℝ)*X 2 0+(2695511141/5000000000 : ℝ)*X 2 1+(-81708879/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4482282367/10000000000 : ℝ)*X 0 0+(852601527/2000000000 : ℝ)*X 0 1+(5328759/12500000 : ℝ)*X 0 2+(4482282367/10000000000 : ℝ)*X 1 0+(852601527/2000000000 : ℝ)*X 1 1+(5328759/12500000 : ℝ)*X 1 2+(4482282367/10000000000 : ℝ)*X 2 0+(852601527/2000000000 : ℝ)*X 2 1+(5328759/12500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-559689211/2500000000 : ℝ)*X 0 0+(1316079389/2500000000 : ℝ)*X 0 1+(2632158889/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((134346807/250000000 : ℝ)*X 1 0+(-83735087/400000000 : ℝ)*X 1 1+(5264317773/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5373872343/10000000000 : ℝ)*X 2 0+(1052863519/2000000000 : ℝ)*X 2 1+(-130836083/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4183764363/10000000000 : ℝ)*X 0 0+(2206105979/5000000000 : ℝ)*X 0 1+(4412211897/10000000000 : ℝ)*X 0 2+(4183764363/10000000000 : ℝ)*X 1 0+(2206105979/5000000000 : ℝ)*X 1 1+(4412211897/10000000000 : ℝ)*X 1 2+(4183764363/10000000000 : ℝ)*X 2 0+(2206105979/5000000000 : ℝ)*X 2 1+(4412211897/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2167122523/10000000000 : ℝ)*X 0 0+(5177215337/10000000000 : ℝ)*X 0 1+(2702525879/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5274908163/10000000000 : ℝ)*X 1 0+(-509244669/2500000000 : ℝ)*X 1 1+(216202081/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5274908201/10000000000 : ℝ)*X 2 0+(5405052083/10000000000 : ℝ)*X 2 1+(-407395709/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2257388641/5000000000 : ℝ)*X 0 0+(4246472439/10000000000 : ℝ)*X 0 1+(106161809/250000000 : ℝ)*X 0 2+(2257388641/5000000000 : ℝ)*X 1 0+(4246472439/10000000000 : ℝ)*X 1 1+(106161809/250000000 : ℝ)*X 1 2+(2257388641/5000000000 : ℝ)*X 2 0+(4246472439/10000000000 : ℝ)*X 2 1+(106161809/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1969322527/10000000000 : ℝ)*X 0 0+(5475858517/10000000000 : ℝ)*X 0 1+(2626635869/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1345409187/2500000000 : ℝ)*X 1 0+(-2097689097/10000000000 : ℝ)*X 1 1+(525327107/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((134540921/250000000 : ℝ)*X 2 0+(525327089/1000000000 : ℝ)*X 2 1+(-1048844607/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((2078645453/5000000000 : ℝ)*X 0 0+(2212604661/5000000000 : ℝ)*X 0 1+(553151309/1250000000 : ℝ)*X 0 2+(2078645453/5000000000 : ℝ)*X 1 0+(2212604661/5000000000 : ℝ)*X 1 1+(553151309/1250000000 : ℝ)*X 1 2+(2078645453/5000000000 : ℝ)*X 2 0+(2212604661/5000000000 : ℝ)*X 2 1+(553151309/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1316_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31423/50000 : ℝ) ≤ (-282874320495906917086767645385479/450125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2004181/50000000000000 : ℝ)*(lower0) + (29247599/100000000000000 : ℝ)*(upper1) + (43046433/100000000000000 : ℝ)*(lower4) + (1445689669560387/50000000000000 : ℝ)*(major0) + (1445689669560387/50000000000000 : ℝ)*(major1) + (1445689669560387/50000000000000 : ℝ)*(major2) + (5137996013/100000000000000 : ℝ)*(sp2) + (1256385821/50000000000000 : ℝ)*(sp3) + (392258096427157/10000000000000 : ℝ)*(sp4) + (3922556263627959/100000000000000 : ℝ)*(sp5) + (490322429677763/12500000000000 : ℝ)*(sp6) + (1881119424578921/100000000000000 : ℝ)*(sp7) + (1805573273/50000000000000 : ℝ)*(sp12) + (14155895079/50000000000000 : ℝ)*(sp13) + (1881121937350563/100000000000000 : ℝ)*(f.failure) + (980646143854529/25000000000000 : ℝ)*(f.sum) + (4371503480211/3601000000000000000000000000 : ℝ)*base66 + (6810132658535917831/900250000000000000000000000000000 : ℝ)*base67 + (4242084230347167831/900250000000000000000000000000000 : ℝ)*base69 + (1489842004523167831/900250000000000000000000000000000 : ℝ)*base71 + (85255158501867/3601000000000000000000000000 : ℝ)*base73 + (365197253257417831/900250000000000000000000000000000 : ℝ)*base75 + (1165807684985667831/900250000000000000000000000000000 : ℝ)*base77 + (52104081107349917831/900250000000000000000000000000000 : ℝ)*base79 + (1662597802923/1800500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (2020449/5000000000000000000000 : ℝ)*base89 + (2020449/5000000000000000000000 : ℝ)*base91 + (2020449/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58891/100000 : ℝ) ≤ (424150484124986207334671361/720200000000000000000000000 : ℝ) := by norm_num
    linear_combination (6838253/20000000000000 : ℝ)*(upper0) + (52766473/100000000000000 : ℝ)*(upper3) + (18695889/10000000000000 : ℝ)*(upper4) + (36990103945141/1250000000000 : ℝ)*(major0) + (36990103945141/1250000000000 : ℝ)*(major1) + (36990103945141/1250000000000 : ℝ)*(major2) + (1986762667854283/50000000000000 : ℝ)*(sp0) + (3973511385872193/100000000000000 : ℝ)*(sp1) + (397351319158373/10000000000000 : ℝ)*(sp2) + (60163967767969/3125000000000 : ℝ)*(sp3) + (5713610417/25000000000000 : ℝ)*(sp5) + (21048730131/100000000000000 : ℝ)*(sp6) + (4278941797/100000000000000 : ℝ)*(sp7) + (1780921059/20000000000000 : ℝ)*(sp8) + (962625623758403/50000000000000 : ℝ)*(f.failure) + (3973534240313861/100000000000000 : ℝ)*(f.sum) + (12663120944271/1800500000000000000000000000 : ℝ)*base65 + (119985153627834017/22506250000000000000000000000000 : ℝ)*base68 + (24568206732665983/22506250000000000000000000000000 : ℝ)*base69 + (139013829152609733/22506250000000000000000000000000 : ℝ)*base71 + (77411819128119/1800500000000000000000000000 : ℝ)*base74 + (37663787196796517/22506250000000000000000000000000 : ℝ)*base76 + (4753266643647233/22506250000000000000000000000000 : ℝ)*base77 + (730896103903921517/22506250000000000000000000000000 : ℝ)*base80 + (19264065507489/3601000000000000000000000000 : ℝ)*base81 + (13000769/2500000000000000000000 : ℝ)*base89 + (13000769/2500000000000000000000 : ℝ)*base91 + (13000769/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (79801/100000 : ℝ) ≤ (359214803996109840867063783702729/450125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5924643/25000000000000 : ℝ)*(lower3) + (53453457/100000000000000 : ℝ)*(upper4) + (44163/1000000000000 : ℝ)*(lower5) + (1636176852373911/50000000000000 : ℝ)*(major0) + (1636176852373911/50000000000000 : ℝ)*(major1) + (1636176852373911/50000000000000 : ℝ)*(major2) + (485550911/6250000000000 : ℝ)*(sp0) + (1690517477/1562500000000 : ℝ)*(sp1) + (145444022089/100000000000000 : ℝ)*(sp2) + (44894214089/100000000000000 : ℝ)*(sp3) + (2194557956406067/50000000000000 : ℝ)*(sp8) + (2194507744254091/50000000000000 : ℝ)*(sp9) + (2194489118802311/50000000000000 : ℝ)*(sp10) + (532234429713421/25000000000000 : ℝ)*(sp11) + (2128982613067773/100000000000000 : ℝ)*(f.failure) + (438912368162671/10000000000000 : ℝ)*(f.sum) + (11331762828307/3601000000000000000000000000 : ℝ)*base65 + (4644688172317390757/900250000000000000000000000000000 : ℝ)*base68 + (534918158168859243/900250000000000000000000000000000 : ℝ)*base69 + (6387832837413609243/900250000000000000000000000000000 : ℝ)*base71 + (2062129463601/3601000000000000000000000000 : ℝ)*base73 + (1527202070135640757/900250000000000000000000000000000 : ℝ)*base76 + (5903687341790890757/900250000000000000000000000000000 : ℝ)*base78 + (5705343087864890757/900250000000000000000000000000000 : ℝ)*base80 + (15114379731437/3601000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (25041279/5000000000000000000000 : ℝ)*base89 + (25041279/5000000000000000000000 : ℝ)*base91 + (25041279/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-337/400 : ℝ) ≤ (-75843882058779863029026453/90025000000000000000000000 : ℝ) := by norm_num
    linear_combination (190250629/100000000000000 : ℝ)*(upper3) + (5327753/3125000000000 : ℝ)*(lower4) + (502815777/100000000000000 : ℝ)*(upper5) + (413569097661489/12500000000000 : ℝ)*(major0) + (413569097661489/12500000000000 : ℝ)*(major1) + (413569097661489/12500000000000 : ℝ)*(major2) + (28795163333/100000000000000 : ℝ)*(sp4) + (472690539979/100000000000000 : ℝ)*(sp5) + (18637381599/2500000000000 : ℝ)*(sp6) + (168234811917/50000000000000 : ℝ)*(sp7) + (35098638121753/781250000000 : ℝ)*(sp12) + (2246090892103869/50000000000000 : ℝ)*(sp13) + (4491908979483757/100000000000000 : ℝ)*(sp14) + (2152197144199041/100000000000000 : ℝ)*(sp15) + (17220268910583/800000000000 : ℝ)*(f.failure) + (1123163618686929/25000000000000 : ℝ)*(f.sum) + (3367890107479/900250000000000000000000000 : ℝ)*base66 + (2620696269192264043/225062500000000000000000000000000 : ℝ)*base68 + (853718663203610957/225062500000000000000000000000000 : ℝ)*base69 + (184022719341139043/225062500000000000000000000000000 : ℝ)*base72 + (28222789717711/3601000000000000000000000000 : ℝ)*base74 + (641414289918548457/225062500000000000000000000000000 : ℝ)*base75 + (795028699692139043/225062500000000000000000000000000 : ℝ)*base78 + (141419890079360957/225062500000000000000000000000000 : ℝ)*base79 + (237315615529/180050000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (150909/40000000000000000000 : ℝ)*base89 + (150909/40000000000000000000 : ℝ)*base91 + (150909/40000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1316_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76852523/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14689/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (693/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31423/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58891/100000 : ℝ) else (79801/100000 : ℝ) ≤ X j i ∧ X j i ≤ (337/400 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1316_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1316_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76852523/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14689/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (693/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31423/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58891/100000 : ℝ) else (79801/100000 : ℝ) ≤ X j i ∧ X j i ≤ (337/400 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1316_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4275/1024 : ℝ) ≤ p) (hpb : p ≤ (1069/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76852523/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14689/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (693/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31423/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58891/100000 : ℝ) else (79801/100000 : ℝ) ≤ X j i ∧ X j i ≤ (337/400 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1316_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
