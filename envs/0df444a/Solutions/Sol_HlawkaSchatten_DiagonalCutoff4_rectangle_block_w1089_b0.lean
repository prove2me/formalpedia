-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1089_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:56:23.432383+00:00
-- url     : https://prove2.me/submissions/2ee793d9-2ea6-4bff-9c24-79f66346ec52

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
theorem support_rectangle_w1089_s0_0 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1908699363/10000000000 : ℝ)*x 0 + (1516665289/2500000000 : ℝ)*x 1 + (4773732677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1908699363/10000000000 : ℝ)^4141 ≤ (11077574826263/100000000000000 : ℝ)^3117 := by
    have hnat : (1908699363 : ℕ)^4141*100000000000000^3117 ≤ 11077574826263^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1908699363 10000000000 11077574826263 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1516665289/2500000000 : ℝ)^4141 ≤ (2574033360569/5000000000000 : ℝ)^3117 := by
    have hnat : (1516665289 : ℕ)^4141*5000000000000^3117 ≤ 2574033360569^3117*2500000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1516665289 2500000000 2574033360569 5000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4773732677/10000000000 : ℝ)^4141 ≤ (37441757948319/100000000000000 : ℝ)^3117 := by
    have hnat : (4773732677 : ℕ)^4141*100000000000000^3117 ≤ 37441757948319^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4773732677 10000000000 37441757948319 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1908699363/10000000000 : ℝ), (1516665289/2500000000 : ℝ), (4773732677/10000000000 : ℝ)] ![(11077574826263/100000000000000 : ℝ), (2574033360569/5000000000000 : ℝ), (37441757948319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1908699363/10000000000 : ℝ)|^4141 ≤ (11077574826263/100000000000000 : ℝ)^3117
        have hw : |(-1908699363/10000000000 : ℝ)|=(1908699363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1516665289/2500000000 : ℝ)|^4141 ≤ (2574033360569/5000000000000 : ℝ)^3117
        have hw : |(1516665289/2500000000 : ℝ)|=(1516665289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4773732677/10000000000 : ℝ)|^4141 ≤ (37441757948319/100000000000000 : ℝ)^3117
        have hw : |(4773732677/10000000000 : ℝ)|=(4773732677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s0_1 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (551977829/1000000000 : ℝ)*x 0 + (-2652236067/10000000000 : ℝ)*x 1 + (596716633/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (551977829/1000000000 : ℝ)^4141 ≤ (45408532588427/100000000000000 : ℝ)^3117 := by
    have hnat : (551977829 : ℕ)^4141*100000000000000^3117 ≤ 45408532588427^3117*1000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551977829 1000000000 45408532588427 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2652236067/10000000000 : ℝ)^4141 ≤ (8574852708989/50000000000000 : ℝ)^3117 := by
    have hnat : (2652236067 : ℕ)^4141*50000000000000^3117 ≤ 8574852708989^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652236067 10000000000 8574852708989 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (596716633/1250000000 : ℝ)^4141 ≤ (2340110123803/6250000000000 : ℝ)^3117 := by
    have hnat : (596716633 : ℕ)^4141*6250000000000^3117 ≤ 2340110123803^3117*1250000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      596716633 1250000000 2340110123803 6250000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(551977829/1000000000 : ℝ), (-2652236067/10000000000 : ℝ), (596716633/1250000000 : ℝ)] ![(45408532588427/100000000000000 : ℝ), (8574852708989/50000000000000 : ℝ), (2340110123803/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(551977829/1000000000 : ℝ)|^4141 ≤ (45408532588427/100000000000000 : ℝ)^3117
        have hw : |(551977829/1000000000 : ℝ)|=(551977829/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2652236067/10000000000 : ℝ)|^4141 ≤ (8574852708989/50000000000000 : ℝ)^3117
        have hw : |(-2652236067/10000000000 : ℝ)|=(2652236067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(596716633/1250000000 : ℝ)|^4141 ≤ (2340110123803/6250000000000 : ℝ)^3117
        have hw : |(596716633/1250000000 : ℝ)|=(596716633/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s0_2 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (275988937/500000000 : ℝ)*x 0 + (2386866393/5000000000 : ℝ)*x 1 + (-2652235831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (275988937/500000000 : ℝ)^4141 ≤ (1135213437663/2500000000000 : ℝ)^3117 := by
    have hnat : (275988937 : ℕ)^4141*2500000000000^3117 ≤ 1135213437663^3117*500000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275988937 500000000 1135213437663 2500000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2386866393/5000000000 : ℝ)^4141 ≤ (585027485689/1562500000000 : ℝ)^3117 := by
    have hnat : (2386866393 : ℕ)^4141*1562500000000^3117 ≤ 585027485689^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2386866393 5000000000 585027485689 1562500000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2652235831/10000000000 : ℝ)^4141 ≤ (8574851695323/50000000000000 : ℝ)^3117 := by
    have hnat : (2652235831 : ℕ)^4141*50000000000000^3117 ≤ 8574851695323^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652235831 10000000000 8574851695323 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(275988937/500000000 : ℝ), (2386866393/5000000000 : ℝ), (-2652235831/10000000000 : ℝ)] ![(1135213437663/2500000000000 : ℝ), (585027485689/1562500000000 : ℝ), (8574851695323/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(275988937/500000000 : ℝ)|^4141 ≤ (1135213437663/2500000000000 : ℝ)^3117
        have hw : |(275988937/500000000 : ℝ)|=(275988937/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2386866393/5000000000 : ℝ)|^4141 ≤ (585027485689/1562500000000 : ℝ)^3117
        have hw : |(2386866393/5000000000 : ℝ)|=(2386866393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2652235831/10000000000 : ℝ)|^4141 ≤ (8574851695323/50000000000000 : ℝ)^3117
        have hw : |(-2652235831/10000000000 : ℝ)|=(2652235831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s0_3 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4205312243/10000000000 : ℝ)*x 0 + (3123662573/10000000000 : ℝ)*x 1 + (708649737/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4205312243/10000000000 : ℝ)^4141 ≤ (31637930409157/100000000000000 : ℝ)^3117 := by
    have hnat : (4205312243 : ℕ)^4141*100000000000000^3117 ≤ 31637930409157^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4205312243 10000000000 31637930409157 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3123662573/10000000000 : ℝ)^4141 ≤ (4262659592017/20000000000000 : ℝ)^3117 := by
    have hnat : (3123662573 : ℕ)^4141*20000000000000^3117 ≤ 4262659592017^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3123662573 10000000000 4262659592017 20000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (708649737/1250000000 : ℝ)^4141 ≤ (47048771623629/100000000000000 : ℝ)^3117 := by
    have hnat : (708649737 : ℕ)^4141*100000000000000^3117 ≤ 47048771623629^3117*1250000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708649737 1250000000 47048771623629 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4205312243/10000000000 : ℝ), (3123662573/10000000000 : ℝ), (708649737/1250000000 : ℝ)] ![(31637930409157/100000000000000 : ℝ), (4262659592017/20000000000000 : ℝ), (47048771623629/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4205312243/10000000000 : ℝ)|^4141 ≤ (31637930409157/100000000000000 : ℝ)^3117
        have hw : |(4205312243/10000000000 : ℝ)|=(4205312243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3123662573/10000000000 : ℝ)|^4141 ≤ (4262659592017/20000000000000 : ℝ)^3117
        have hw : |(3123662573/10000000000 : ℝ)|=(3123662573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(708649737/1250000000 : ℝ)|^4141 ≤ (47048771623629/100000000000000 : ℝ)^3117
        have hw : |(708649737/1250000000 : ℝ)|=(708649737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s0_4 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1914003159/10000000000 : ℝ)*x 0 + (600888657/1250000000 : ℝ)*x 1 + (6032115023/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1914003159/10000000000 : ℝ)^4141 ≤ (2223697549011/20000000000000 : ℝ)^3117 := by
    have hnat : (1914003159 : ℕ)^4141*20000000000000^3117 ≤ 2223697549011^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1914003159 10000000000 2223697549011 20000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (600888657/1250000000 : ℝ)^4141 ≤ (9447484942329/25000000000000 : ℝ)^3117 := by
    have hnat : (600888657 : ℕ)^4141*25000000000000^3117 ≤ 9447484942329^3117*1250000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600888657 1250000000 9447484942329 25000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6032115023/10000000000 : ℝ)^4141 ≤ (51091572469437/100000000000000 : ℝ)^3117 := by
    have hnat : (6032115023 : ℕ)^4141*100000000000000^3117 ≤ 51091572469437^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6032115023 10000000000 51091572469437 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1914003159/10000000000 : ℝ), (600888657/1250000000 : ℝ), (6032115023/10000000000 : ℝ)] ![(2223697549011/20000000000000 : ℝ), (9447484942329/25000000000000 : ℝ), (51091572469437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1914003159/10000000000 : ℝ)|^4141 ≤ (2223697549011/20000000000000 : ℝ)^3117
        have hw : |(-1914003159/10000000000 : ℝ)|=(1914003159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(600888657/1250000000 : ℝ)|^4141 ≤ (9447484942329/25000000000000 : ℝ)^3117
        have hw : |(600888657/1250000000 : ℝ)|=(600888657/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6032115023/10000000000 : ℝ)|^4141 ≤ (51091572469437/100000000000000 : ℝ)^3117
        have hw : |(6032115023/10000000000 : ℝ)|=(6032115023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s0_5 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5168733057/10000000000 : ℝ)*x 0 + (-1393856387/10000000000 : ℝ)*x 1 + (6032114161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5168733057/10000000000 : ℝ)^4141 ≤ (2600786940113/6250000000000 : ℝ)^3117 := by
    have hnat : (5168733057 : ℕ)^4141*6250000000000^3117 ≤ 2600786940113^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168733057 10000000000 2600786940113 6250000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1393856387/10000000000 : ℝ)^4141 ≤ (729584617721/10000000000000 : ℝ)^3117 := by
    have hnat : (1393856387 : ℕ)^4141*10000000000000^3117 ≤ 729584617721^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1393856387 10000000000 729584617721 10000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6032114161/10000000000 : ℝ)^4141 ≤ (51091562769803/100000000000000 : ℝ)^3117 := by
    have hnat : (6032114161 : ℕ)^4141*100000000000000^3117 ≤ 51091562769803^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6032114161 10000000000 51091562769803 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5168733057/10000000000 : ℝ), (-1393856387/10000000000 : ℝ), (6032114161/10000000000 : ℝ)] ![(2600786940113/6250000000000 : ℝ), (729584617721/10000000000000 : ℝ), (51091562769803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5168733057/10000000000 : ℝ)|^4141 ≤ (2600786940113/6250000000000 : ℝ)^3117
        have hw : |(5168733057/10000000000 : ℝ)|=(5168733057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1393856387/10000000000 : ℝ)|^4141 ≤ (729584617721/10000000000000 : ℝ)^3117
        have hw : |(-1393856387/10000000000 : ℝ)|=(1393856387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6032114161/10000000000 : ℝ)|^4141 ≤ (51091562769803/100000000000000 : ℝ)^3117
        have hw : |(6032114161/10000000000 : ℝ)|=(6032114161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s0_6 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5168733449/10000000000 : ℝ)*x 0 + (6032115089/10000000000 : ℝ)*x 1 + (-696927141/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5168733449/10000000000 : ℝ)^4141 ≤ (41612595234521/100000000000000 : ℝ)^3117 := by
    have hnat : (5168733449 : ℕ)^4141*100000000000000^3117 ≤ 41612595234521^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168733449 10000000000 41612595234521 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6032115089/10000000000 : ℝ)^4141 ≤ (51091573212101/100000000000000 : ℝ)^3117 := by
    have hnat : (6032115089 : ℕ)^4141*100000000000000^3117 ≤ 51091573212101^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6032115089 10000000000 51091573212101 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (696927141/5000000000 : ℝ)^4141 ≤ (3647915769667/50000000000000 : ℝ)^3117 := by
    have hnat : (696927141 : ℕ)^4141*50000000000000^3117 ≤ 3647915769667^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      696927141 5000000000 3647915769667 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5168733449/10000000000 : ℝ), (6032115089/10000000000 : ℝ), (-696927141/5000000000 : ℝ)] ![(41612595234521/100000000000000 : ℝ), (51091573212101/100000000000000 : ℝ), (3647915769667/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5168733449/10000000000 : ℝ)|^4141 ≤ (41612595234521/100000000000000 : ℝ)^3117
        have hw : |(5168733449/10000000000 : ℝ)|=(5168733449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6032115089/10000000000 : ℝ)|^4141 ≤ (51091573212101/100000000000000 : ℝ)^3117
        have hw : |(6032115089/10000000000 : ℝ)|=(6032115089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-696927141/5000000000 : ℝ)|^4141 ≤ (3647915769667/50000000000000 : ℝ)^3117
        have hw : |(-696927141/5000000000 : ℝ)|=(696927141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s0_7 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4215752309/10000000000 : ℝ)*x 0 + (1120696941/2000000000 : ℝ)*x 1 + (3191678697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4215752309/10000000000 : ℝ)^4141 ≤ (253938562429/800000000000 : ℝ)^3117 := by
    have hnat : (4215752309 : ℕ)^4141*800000000000^3117 ≤ 253938562429^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4215752309 10000000000 253938562429 800000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120696941/2000000000 : ℝ)^4141 ≤ (23162819614347/50000000000000 : ℝ)^3117 := by
    have hnat : (1120696941 : ℕ)^4141*50000000000000^3117 ≤ 23162819614347^3117*2000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120696941 2000000000 23162819614347 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3191678697/10000000000 : ℝ)^4141 ≤ (5483010111697/25000000000000 : ℝ)^3117 := by
    have hnat : (3191678697 : ℕ)^4141*25000000000000^3117 ≤ 5483010111697^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3191678697 10000000000 5483010111697 25000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4215752309/10000000000 : ℝ), (1120696941/2000000000 : ℝ), (3191678697/10000000000 : ℝ)] ![(253938562429/800000000000 : ℝ), (23162819614347/50000000000000 : ℝ), (5483010111697/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4215752309/10000000000 : ℝ)|^4141 ≤ (253938562429/800000000000 : ℝ)^3117
        have hw : |(4215752309/10000000000 : ℝ)|=(4215752309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1120696941/2000000000 : ℝ)|^4141 ≤ (23162819614347/50000000000000 : ℝ)^3117
        have hw : |(1120696941/2000000000 : ℝ)|=(1120696941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3191678697/10000000000 : ℝ)|^4141 ≤ (5483010111697/25000000000000 : ℝ)^3117
        have hw : |(3191678697/10000000000 : ℝ)|=(3191678697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1089_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148440671/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (193/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1401/5000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (8281/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8281 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8281*1^2048 ≤ 0^2048*1^8281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8281 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8281/2048 : ℝ) ≤ (2460065519474530639/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8281 ≤ (2460065519474530639/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8281*100000000000000000000^2048 ≤ 2460065519474530639^2048*5^8281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2460065519474530639 100000000000000000000 8281 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2460065519474530639/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8281/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8281 := by
      have hnat : (1 : ℕ)^2048*1^8281 ≤ 1^8281*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102460065519474530639/100000000000000000000 : ℝ) ≤ (2012057065985413/2000000000000000 : ℝ) ^ (8281/2048 : ℝ) := by
    have hpowers : (102460065519474530639/100000000000000000000 : ℝ)^2048 ≤ (2012057065985413/2000000000000000 : ℝ)^8281 := by
      have hnat : (102460065519474530639 : ℕ)^2048*2000000000000000^8281 ≤ 2012057065985413^8281*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102460065519474530639 100000000000000000000 2012057065985413 2000000000000000 2048 8281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2012057065985413/2000000000000000 : ℝ)) (X := (102460065519474530639/100000000000000000000 : ℝ)) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52460065519474530639/50000000000000000000 : ℝ) ≤ (1012057065985413/1000000000000000 : ℝ) ^ (8281/2048 : ℝ) := by
    have hpowers : (52460065519474530639/50000000000000000000 : ℝ)^2048 ≤ (1012057065985413/1000000000000000 : ℝ)^8281 := by
      have hnat : (52460065519474530639 : ℕ)^2048*1000000000000000^8281 ≤ 1012057065985413^8281*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52460065519474530639 50000000000000000000 1012057065985413 1000000000000000 2048 8281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1012057065985413/1000000000000000 : ℝ)) (X := (52460065519474530639/50000000000000000000 : ℝ)) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(12057065985413/800000000000000 : ℝ)*(0 : ℝ))^(8281/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(12057065985413/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2460065519474530639/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(12057065985413/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8281/2048 : ℝ) := by
    rw [show (1 : ℝ)+(12057065985413/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2012057065985413/2000000000000000 : ℝ) by norm_num, show 1+(2460065519474530639/100000000000000000000 : ℝ)+(0 : ℝ)=(102460065519474530639/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2460065519474530639/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(12057065985413/800000000000000 : ℝ)*(2/5 : ℝ))^(8281/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(12057065985413/800000000000000 : ℝ)*(2/5 : ℝ)=(1012057065985413/1000000000000000 : ℝ) by norm_num, show 1+2*(2460065519474530639/100000000000000000000 : ℝ)=(52460065519474530639/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(12057065985413/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8281/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12057065985413/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(12057065985413/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8281/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12057065985413/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(12057065985413/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8281/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (12057065985413/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1908699363/10000000000 : ℝ)*X 0 0+(1516665289/2500000000 : ℝ)*X 0 1+(4773732677/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((551977829/1000000000 : ℝ)*X 1 0+(-2652236067/10000000000 : ℝ)*X 1 1+(596716633/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((275988937/500000000 : ℝ)*X 2 0+(2386866393/5000000000 : ℝ)*X 2 1+(-2652235831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4205312243/10000000000 : ℝ)*X 0 0+(3123662573/10000000000 : ℝ)*X 0 1+(708649737/1250000000 : ℝ)*X 0 2+(4205312243/10000000000 : ℝ)*X 1 0+(3123662573/10000000000 : ℝ)*X 1 1+(708649737/1250000000 : ℝ)*X 1 2+(4205312243/10000000000 : ℝ)*X 2 0+(3123662573/10000000000 : ℝ)*X 2 1+(708649737/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1914003159/10000000000 : ℝ)*X 0 0+(600888657/1250000000 : ℝ)*X 0 1+(6032115023/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5168733057/10000000000 : ℝ)*X 1 0+(-1393856387/10000000000 : ℝ)*X 1 1+(6032114161/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5168733449/10000000000 : ℝ)*X 2 0+(6032115089/10000000000 : ℝ)*X 2 1+(-696927141/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4215752309/10000000000 : ℝ)*X 0 0+(1120696941/2000000000 : ℝ)*X 0 1+(3191678697/10000000000 : ℝ)*X 0 2+(4215752309/10000000000 : ℝ)*X 1 0+(1120696941/2000000000 : ℝ)*X 1 1+(3191678697/10000000000 : ℝ)*X 1 2+(4215752309/10000000000 : ℝ)*X 2 0+(1120696941/2000000000 : ℝ)*X 2 1+(3191678697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15165672093303408389253/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19095819/50000000000000 : ℝ)*(base1) + (81327561/5000000000000 : ℝ)*(base19) + (774369127/50000000000000 : ℝ)*(base23) + (70434063/50000000000000 : ℝ)*(base24) + (392177827/100000000000000 : ℝ)*(upper3) + (36446781030273/6250000000000 : ℝ)*(major0) + (36446781030273/6250000000000 : ℝ)*(major1) + (36446781030273/6250000000000 : ℝ)*(major2) + (38672177747267/5000000000000 : ℝ)*(sp0) + (386722810996777/50000000000000 : ℝ)*(sp1) + (154689111787679/20000000000000 : ℝ)*(sp2) + (49105805943747/12500000000000 : ℝ)*(sp3) + (3731791073/100000000000000 : ℝ)*(sp4) + (1528236691/50000000000000 : ℝ)*(sp7) + (98212385553749/25000000000000 : ℝ)*(f.failure) + (386723624272387/50000000000000 : ℝ)*(f.sum) + (1093063539751/2500000000000000000000000000 : ℝ)*base66 + (5698647022251/5000000000000000000000000000 : ℝ)*base68 + (9271836362749/5000000000000000000000000000 : ℝ)*base69 + (25964940077749/5000000000000000000000000000 : ℝ)*base71 + (5872266692251/2500000000000000000000000000 : ℝ)*base74 + (30885813377749/5000000000000000000000000000 : ℝ)*base75 + (6957041877749/5000000000000000000000000000 : ℝ)*base77 + (8261184267749/5000000000000000000000000000 : ℝ)*base79 + (10288223145249/2500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (8125579/2500000000000000000000 : ℝ)*base89 + (8125579/2500000000000000000000 : ℝ)*base91 + (8125579/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (339151361132060697089121/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (427824171/25000000000000 : ℝ)*(base19) + (2065575667/100000000000000 : ℝ)*(base23) + (247601497/100000000000000 : ℝ)*(base39) + (418570837/100000000000000 : ℝ)*(base45) + (19008549/10000000000000 : ℝ)*(upper3) + (74153383/20000000000000 : ℝ)*(upper5) + (307736006951543/50000000000000 : ℝ)*(major0) + (307736006951543/50000000000000 : ℝ)*(major1) + (615471766301589/100000000000000 : ℝ)*(major2) + (9568143/1250000000000 : ℝ)*(sp2) + (102039822153371/12500000000000 : ℝ)*(sp4) + (204079216482571/25000000000000 : ℝ)*(sp5) + (408157996900679/50000000000000 : ℝ)*(sp6) + (41462492035157/10000000000000 : ℝ)*(sp7) + (41462492035157/10000000000000 : ℝ)*(f.failure) + (163263764965693/20000000000000 : ℝ)*(f.sum) + (5020838121369/3200000000000000000000000000 : ℝ)*base66 + (595554620081257/80000000000000000000000000000 : ℝ)*base67 + (15302346317741/40000000000000000000000000000 : ℝ)*base70 + (284824967281257/80000000000000000000000000000 : ℝ)*base71 + (5986106761831/3200000000000000000000000000 : ℝ)*base73 + (176633195282259/40000000000000000000000000000 : ℝ)*base75 + (144024056962259/40000000000000000000000000000 : ℝ)*base77 + (147733853762259/40000000000000000000000000000 : ℝ)*base79 + (514581962259/20000000000000000000000000000 : ℝ)*base81 + (670347/1000000000000000000000 : ℝ)*base89 + (670347/1000000000000000000000 : ℝ)*base91 + (670347/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1089_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148440671/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (193/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1401/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1089_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1089_s1_0 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-529294643/2500000000 : ℝ)*x 0 + (1143185701/2000000000 : ℝ)*x 1 + (4990969803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529294643/2500000000 : ℝ)^4141 ≤ (6356596745283/50000000000000 : ℝ)^3117 := by
    have hnat : (529294643 : ℕ)^4141*50000000000000^3117 ≤ 6356596745283^3117*2500000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529294643 2500000000 6356596745283 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1143185701/2000000000 : ℝ)^4141 ≤ (190258769947/400000000000 : ℝ)^3117 := by
    have hnat : (1143185701 : ℕ)^4141*400000000000^3117 ≤ 190258769947^3117*2000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143185701 2000000000 190258769947 400000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4990969803/10000000000 : ℝ)^4141 ≤ (3972211400259/10000000000000 : ℝ)^3117 := by
    have hnat : (4990969803 : ℕ)^4141*10000000000000^3117 ≤ 3972211400259^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4990969803 10000000000 3972211400259 10000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-529294643/2500000000 : ℝ), (1143185701/2000000000 : ℝ), (4990969803/10000000000 : ℝ)] ![(6356596745283/50000000000000 : ℝ), (190258769947/400000000000 : ℝ), (3972211400259/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-529294643/2500000000 : ℝ)|^4141 ≤ (6356596745283/50000000000000 : ℝ)^3117
        have hw : |(-529294643/2500000000 : ℝ)|=(529294643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1143185701/2000000000 : ℝ)|^4141 ≤ (190258769947/400000000000 : ℝ)^3117
        have hw : |(1143185701/2000000000 : ℝ)|=(1143185701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4990969803/10000000000 : ℝ)|^4141 ≤ (3972211400259/10000000000000 : ℝ)^3117
        have hw : |(4990969803/10000000000 : ℝ)|=(4990969803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s1_1 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5422044457/10000000000 : ℝ)*x 0 + (-501896557/2000000000 : ℝ)*x 1 + (1247742507/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5422044457/10000000000 : ℝ)^4141 ≤ (11085877274847/25000000000000 : ℝ)^3117 := by
    have hnat : (5422044457 : ℕ)^4141*25000000000000^3117 ≤ 11085877274847^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422044457 10000000000 11085877274847 25000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (501896557/2000000000 : ℝ)^4141 ≤ (15934374509839/100000000000000 : ℝ)^3117 := by
    have hnat : (501896557 : ℕ)^4141*100000000000000^3117 ≤ 15934374509839^3117*2000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501896557 2000000000 15934374509839 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1247742507/2500000000 : ℝ)^4141 ≤ (9930529095403/25000000000000 : ℝ)^3117 := by
    have hnat : (1247742507 : ℕ)^4141*25000000000000^3117 ≤ 9930529095403^3117*2500000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1247742507 2500000000 9930529095403 25000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5422044457/10000000000 : ℝ), (-501896557/2000000000 : ℝ), (1247742507/2500000000 : ℝ)] ![(11085877274847/25000000000000 : ℝ), (15934374509839/100000000000000 : ℝ), (9930529095403/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5422044457/10000000000 : ℝ)|^4141 ≤ (11085877274847/25000000000000 : ℝ)^3117
        have hw : |(5422044457/10000000000 : ℝ)|=(5422044457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-501896557/2000000000 : ℝ)|^4141 ≤ (15934374509839/100000000000000 : ℝ)^3117
        have hw : |(-501896557/2000000000 : ℝ)|=(501896557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1247742507/2500000000 : ℝ)|^4141 ≤ (9930529095403/25000000000000 : ℝ)^3117
        have hw : |(1247742507/2500000000 : ℝ)|=(1247742507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s1_2 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (677755667/1250000000 : ℝ)*x 0 + (2495484561/5000000000 : ℝ)*x 1 + (-2509482787/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (677755667/1250000000 : ℝ)^4141 ≤ (5542939831231/12500000000000 : ℝ)^3117 := by
    have hnat : (677755667 : ℕ)^4141*12500000000000^3117 ≤ 5542939831231^3117*1250000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      677755667 1250000000 5542939831231 12500000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2495484561/5000000000 : ℝ)^4141 ≤ (7944421360417/20000000000000 : ℝ)^3117 := by
    have hnat : (2495484561 : ℕ)^4141*20000000000000^3117 ≤ 7944421360417^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2495484561 5000000000 7944421360417 20000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2509482787/10000000000 : ℝ)^4141 ≤ (15934374526711/100000000000000 : ℝ)^3117 := by
    have hnat : (2509482787 : ℕ)^4141*100000000000000^3117 ≤ 15934374526711^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2509482787 10000000000 15934374526711 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(677755667/1250000000 : ℝ), (2495484561/5000000000 : ℝ), (-2509482787/10000000000 : ℝ)] ![(5542939831231/12500000000000 : ℝ), (7944421360417/20000000000000 : ℝ), (15934374526711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(677755667/1250000000 : ℝ)|^4141 ≤ (5542939831231/12500000000000 : ℝ)^3117
        have hw : |(677755667/1250000000 : ℝ)|=(677755667/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2495484561/5000000000 : ℝ)|^4141 ≤ (7944421360417/20000000000000 : ℝ)^3117
        have hw : |(2495484561/5000000000 : ℝ)|=(2495484561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2509482787/10000000000 : ℝ)|^4141 ≤ (15934374526711/100000000000000 : ℝ)^3117
        have hw : |(-2509482787/10000000000 : ℝ)|=(2509482787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s1_3 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1080472219/2500000000 : ℝ)*x 0 + (114592311/312500000 : ℝ)*x 1 + (5094260899/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080472219/2500000000 : ℝ)^4141 ≤ (8202093680311/25000000000000 : ℝ)^3117 := by
    have hnat : (1080472219 : ℕ)^4141*25000000000000^3117 ≤ 8202093680311^3117*2500000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080472219 2500000000 8202093680311 25000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (114592311/312500000 : ℝ)^4141 ≤ (824177330463/3125000000000 : ℝ)^3117 := by
    have hnat : (114592311 : ℕ)^4141*3125000000000^3117 ≤ 824177330463^3117*312500000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      114592311 312500000 824177330463 3125000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5094260899/10000000000 : ℝ)^4141 ≤ (2040897534317/5000000000000 : ℝ)^3117 := by
    have hnat : (5094260899 : ℕ)^4141*5000000000000^3117 ≤ 2040897534317^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5094260899 10000000000 2040897534317 5000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080472219/2500000000 : ℝ), (114592311/312500000 : ℝ), (5094260899/10000000000 : ℝ)] ![(8202093680311/25000000000000 : ℝ), (824177330463/3125000000000 : ℝ), (2040897534317/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080472219/2500000000 : ℝ)|^4141 ≤ (8202093680311/25000000000000 : ℝ)^3117
        have hw : |(1080472219/2500000000 : ℝ)|=(1080472219/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(114592311/312500000 : ℝ)|^4141 ≤ (824177330463/3125000000000 : ℝ)^3117
        have hw : |(114592311/312500000 : ℝ)|=(114592311/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5094260899/10000000000 : ℝ)|^4141 ≤ (2040897534317/5000000000000 : ℝ)^3117
        have hw : |(5094260899/10000000000 : ℝ)|=(5094260899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s1_4 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-264758197/1250000000 : ℝ)*x 0 + (1250267573/2500000000 : ℝ)*x 1 + (2852810901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264758197/1250000000 : ℝ)^4141 ≤ (12720270032051/100000000000000 : ℝ)^3117 := by
    have hnat : (264758197 : ℕ)^4141*100000000000000^3117 ≤ 12720270032051^3117*1250000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264758197 1250000000 12720270032051 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1250267573/2500000000 : ℝ)^4141 ≤ (39828946288089/100000000000000 : ℝ)^3117 := by
    have hnat : (1250267573 : ℕ)^4141*100000000000000^3117 ≤ 39828946288089^3117*2500000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1250267573 2500000000 39828946288089 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2852810901/5000000000 : ℝ)^4141 ≤ (4745078365661/10000000000000 : ℝ)^3117 := by
    have hnat : (2852810901 : ℕ)^4141*10000000000000^3117 ≤ 4745078365661^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2852810901 5000000000 4745078365661 10000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-264758197/1250000000 : ℝ), (1250267573/2500000000 : ℝ), (2852810901/5000000000 : ℝ)] ![(12720270032051/100000000000000 : ℝ), (39828946288089/100000000000000 : ℝ), (4745078365661/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-264758197/1250000000 : ℝ)|^4141 ≤ (12720270032051/100000000000000 : ℝ)^3117
        have hw : |(-264758197/1250000000 : ℝ)|=(264758197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1250267573/2500000000 : ℝ)|^4141 ≤ (39828946288089/100000000000000 : ℝ)^3117
        have hw : |(1250267573/2500000000 : ℝ)|=(1250267573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2852810901/5000000000 : ℝ)|^4141 ≤ (4745078365661/10000000000000 : ℝ)^3117
        have hw : |(2852810901/5000000000 : ℝ)|=(2852810901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s1_5 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1309169731/2500000000 : ℝ)*x 0 + (-1794828039/10000000000 : ℝ)*x 1 + (5705624191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1309169731/2500000000 : ℝ)^4141 ≤ (8468176812753/20000000000000 : ℝ)^3117 := by
    have hnat : (1309169731 : ℕ)^4141*20000000000000^3117 ≤ 8468176812753^3117*2500000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309169731 2500000000 8468176812753 20000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1794828039/10000000000 : ℝ)^4141 ≤ (10208305874081/100000000000000 : ℝ)^3117 := by
    have hnat : (1794828039 : ℕ)^4141*100000000000000^3117 ≤ 10208305874081^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1794828039 10000000000 10208305874081 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5705624191/10000000000 : ℝ)^4141 ≤ (47450810051813/100000000000000 : ℝ)^3117 := by
    have hnat : (5705624191 : ℕ)^4141*100000000000000^3117 ≤ 47450810051813^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5705624191 10000000000 47450810051813 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1309169731/2500000000 : ℝ), (-1794828039/10000000000 : ℝ), (5705624191/10000000000 : ℝ)] ![(8468176812753/20000000000000 : ℝ), (10208305874081/100000000000000 : ℝ), (47450810051813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1309169731/2500000000 : ℝ)|^4141 ≤ (8468176812753/20000000000000 : ℝ)^3117
        have hw : |(1309169731/2500000000 : ℝ)|=(1309169731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1794828039/10000000000 : ℝ)|^4141 ≤ (10208305874081/100000000000000 : ℝ)^3117
        have hw : |(-1794828039/10000000000 : ℝ)|=(1794828039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5705624191/10000000000 : ℝ)|^4141 ≤ (47450810051813/100000000000000 : ℝ)^3117
        have hw : |(5705624191/10000000000 : ℝ)|=(5705624191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s1_6 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (163646151/312500000 : ℝ)*x 0 + (5705626543/10000000000 : ℝ)*x 1 + (-897413787/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (163646151/312500000 : ℝ)^4141 ≤ (21170430796081/50000000000000 : ℝ)^3117 := by
    have hnat : (163646151 : ℕ)^4141*50000000000000^3117 ≤ 21170430796081^3117*312500000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163646151 312500000 21170430796081 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5705626543/10000000000 : ℝ)^4141 ≤ (47450836038221/100000000000000 : ℝ)^3117 := by
    have hnat : (5705626543 : ℕ)^4141*100000000000000^3117 ≤ 47450836038221^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5705626543 10000000000 47450836038221 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (897413787/5000000000 : ℝ)^4141 ≤ (5104151180241/50000000000000 : ℝ)^3117 := by
    have hnat : (897413787 : ℕ)^4141*50000000000000^3117 ≤ 5104151180241^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      897413787 5000000000 5104151180241 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(163646151/312500000 : ℝ), (5705626543/10000000000 : ℝ), (-897413787/5000000000 : ℝ)] ![(21170430796081/50000000000000 : ℝ), (47450836038221/100000000000000 : ℝ), (5104151180241/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(163646151/312500000 : ℝ)|^4141 ≤ (21170430796081/50000000000000 : ℝ)^3117
        have hw : |(163646151/312500000 : ℝ)|=(163646151/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5705626543/10000000000 : ℝ)|^4141 ≤ (47450836038221/100000000000000 : ℝ)^3117
        have hw : |(5705626543/10000000000 : ℝ)|=(5705626543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-897413787/5000000000 : ℝ)|^4141 ≤ (5104151180241/50000000000000 : ℝ)^3117
        have hw : |(-897413787/5000000000 : ℝ)|=(897413787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s1_7 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (432362993/1000000000 : ℝ)*x 0 + (5074371679/10000000000 : ℝ)*x 1 + (3687241157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (432362993/1000000000 : ℝ)^4141 ≤ (32825934560029/100000000000000 : ℝ)^3117 := by
    have hnat : (432362993 : ℕ)^4141*100000000000000^3117 ≤ 32825934560029^3117*1000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      432362993 1000000000 32825934560029 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5074371679/10000000000 : ℝ)^4141 ≤ (10151592339247/25000000000000 : ℝ)^3117 := by
    have hnat : (5074371679 : ℕ)^4141*25000000000000^3117 ≤ 10151592339247^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5074371679 10000000000 10151592339247 25000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3687241157/10000000000 : ℝ)^4141 ≤ (1062707842611/4000000000000 : ℝ)^3117 := by
    have hnat : (3687241157 : ℕ)^4141*4000000000000^3117 ≤ 1062707842611^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3687241157 10000000000 1062707842611 4000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(432362993/1000000000 : ℝ), (5074371679/10000000000 : ℝ), (3687241157/10000000000 : ℝ)] ![(32825934560029/100000000000000 : ℝ), (10151592339247/25000000000000 : ℝ), (1062707842611/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(432362993/1000000000 : ℝ)|^4141 ≤ (32825934560029/100000000000000 : ℝ)^3117
        have hw : |(432362993/1000000000 : ℝ)|=(432362993/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5074371679/10000000000 : ℝ)|^4141 ≤ (10151592339247/25000000000000 : ℝ)^3117
        have hw : |(5074371679/10000000000 : ℝ)|=(5074371679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3687241157/10000000000 : ℝ)|^4141 ≤ (1062707842611/4000000000000 : ℝ)^3117
        have hw : |(3687241157/10000000000 : ℝ)|=(3687241157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s1_8 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3925601/5000000000 : ℝ)*x 0 + (5489937633/10000000000 : ℝ)*x 1 + (6368397567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3925601/5000000000 : ℝ)^4141 ≤ (749648071/10000000000000 : ℝ)^3117 := by
    have hnat : (3925601 : ℕ)^4141*10000000000000^3117 ≤ 749648071^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3925601 5000000000 749648071 10000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5489937633/10000000000 : ℝ)^4141 ≤ (901653822563/2000000000000 : ℝ)^3117 := by
    have hnat : (5489937633 : ℕ)^4141*2000000000000^3117 ≤ 901653822563^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5489937633 10000000000 901653822563 2000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6368397567/10000000000 : ℝ)^4141 ≤ (54909812381881/100000000000000 : ℝ)^3117 := by
    have hnat : (6368397567 : ℕ)^4141*100000000000000^3117 ≤ 54909812381881^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6368397567 10000000000 54909812381881 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3925601/5000000000 : ℝ), (5489937633/10000000000 : ℝ), (6368397567/10000000000 : ℝ)] ![(749648071/10000000000000 : ℝ), (901653822563/2000000000000 : ℝ), (54909812381881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3925601/5000000000 : ℝ)|^4141 ≤ (749648071/10000000000000 : ℝ)^3117
        have hw : |(3925601/5000000000 : ℝ)|=(3925601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5489937633/10000000000 : ℝ)|^4141 ≤ (901653822563/2000000000000 : ℝ)^3117
        have hw : |(5489937633/10000000000 : ℝ)|=(5489937633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6368397567/10000000000 : ℝ)|^4141 ≤ (54909812381881/100000000000000 : ℝ)^3117
        have hw : |(6368397567/10000000000 : ℝ)|=(6368397567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s1_9 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (193755881/2000000000 : ℝ)*x 0 + (-4443960703/10000000000 : ℝ)*x 1 + (6931776193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (193755881/2000000000 : ℝ)^4141 ≤ (2249823649573/50000000000000 : ℝ)^3117 := by
    have hnat : (193755881 : ℕ)^4141*50000000000000^3117 ≤ 2249823649573^3117*2000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      193755881 2000000000 2249823649573 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4443960703/10000000000 : ℝ)^4141 ≤ (6809031100633/20000000000000 : ℝ)^3117 := by
    have hnat : (4443960703 : ℕ)^4141*20000000000000^3117 ≤ 6809031100633^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4443960703 10000000000 6809031100633 20000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6931776193/10000000000 : ℝ)^4141 ≤ (6145519718801/10000000000000 : ℝ)^3117 := by
    have hnat : (6931776193 : ℕ)^4141*10000000000000^3117 ≤ 6145519718801^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6931776193 10000000000 6145519718801 10000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(193755881/2000000000 : ℝ), (-4443960703/10000000000 : ℝ), (6931776193/10000000000 : ℝ)] ![(2249823649573/50000000000000 : ℝ), (6809031100633/20000000000000 : ℝ), (6145519718801/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(193755881/2000000000 : ℝ)|^4141 ≤ (2249823649573/50000000000000 : ℝ)^3117
        have hw : |(193755881/2000000000 : ℝ)|=(193755881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4443960703/10000000000 : ℝ)|^4141 ≤ (6809031100633/20000000000000 : ℝ)^3117
        have hw : |(-4443960703/10000000000 : ℝ)|=(4443960703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6931776193/10000000000 : ℝ)|^4141 ≤ (6145519718801/10000000000000 : ℝ)^3117
        have hw : |(6931776193/10000000000 : ℝ)|=(6931776193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s1_10 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (968772399/10000000000 : ℝ)*x 0 + (6931760797/10000000000 : ℝ)*x 1 + (-4443982767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (968772399/10000000000 : ℝ)^4141 ≤ (4499604068511/100000000000000 : ℝ)^3117 := by
    have hnat : (968772399 : ℕ)^4141*100000000000000^3117 ≤ 4499604068511^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      968772399 10000000000 4499604068511 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6931760797/10000000000 : ℝ)^4141 ≤ (61455015849411/100000000000000 : ℝ)^3117 := by
    have hnat : (6931760797 : ℕ)^4141*100000000000000^3117 ≤ 61455015849411^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6931760797 10000000000 61455015849411 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4443982767/10000000000 : ℝ)^4141 ≤ (6809076013227/20000000000000 : ℝ)^3117 := by
    have hnat : (4443982767 : ℕ)^4141*20000000000000^3117 ≤ 6809076013227^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4443982767 10000000000 6809076013227 20000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(968772399/10000000000 : ℝ), (6931760797/10000000000 : ℝ), (-4443982767/10000000000 : ℝ)] ![(4499604068511/100000000000000 : ℝ), (61455015849411/100000000000000 : ℝ), (6809076013227/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(968772399/10000000000 : ℝ)|^4141 ≤ (4499604068511/100000000000000 : ℝ)^3117
        have hw : |(968772399/10000000000 : ℝ)|=(968772399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6931760797/10000000000 : ℝ)|^4141 ≤ (61455015849411/100000000000000 : ℝ)^3117
        have hw : |(6931760797/10000000000 : ℝ)|=(6931760797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4443982767/10000000000 : ℝ)|^4141 ≤ (6809076013227/20000000000000 : ℝ)^3117
        have hw : |(-4443982767/10000000000 : ℝ)|=(4443982767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s1_11 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1922292943/10000000000 : ℝ)*x 0 + (291244811/500000000 : ℝ)*x 1 + (1255354621/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1922292943/10000000000 : ℝ)^4141 ≤ (11182508866447/100000000000000 : ℝ)^3117 := by
    have hnat : (1922292943 : ℕ)^4141*100000000000000^3117 ≤ 11182508866447^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1922292943 10000000000 11182508866447 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (291244811/500000000 : ℝ)^4141 ≤ (24386553984617/50000000000000 : ℝ)^3117 := by
    have hnat : (291244811 : ℕ)^4141*50000000000000^3117 ≤ 24386553984617^3117*500000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291244811 500000000 24386553984617 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1255354621/2500000000 : ℝ)^4141 ≤ (4004438314679/10000000000000 : ℝ)^3117 := by
    have hnat : (1255354621 : ℕ)^4141*10000000000000^3117 ≤ 4004438314679^3117*2500000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255354621 2500000000 4004438314679 10000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1922292943/10000000000 : ℝ), (291244811/500000000 : ℝ), (1255354621/2500000000 : ℝ)] ![(11182508866447/100000000000000 : ℝ), (24386553984617/50000000000000 : ℝ), (4004438314679/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1922292943/10000000000 : ℝ)|^4141 ≤ (11182508866447/100000000000000 : ℝ)^3117
        have hw : |(1922292943/10000000000 : ℝ)|=(1922292943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(291244811/500000000 : ℝ)|^4141 ≤ (24386553984617/50000000000000 : ℝ)^3117
        have hw : |(291244811/500000000 : ℝ)|=(291244811/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1255354621/2500000000 : ℝ)|^4141 ≤ (4004438314679/10000000000000 : ℝ)^3117
        have hw : |(1255354621/2500000000 : ℝ)|=(1255354621/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1089_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148440671/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1401/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (193/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5347/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10341/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1401/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (193/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1401/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (193/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1401/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (193/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1401/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (193/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1401/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (193/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1401/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (193/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (193/100000 : ℝ) ^ (8281/2048 : ℝ) ≤ (2065369/195312500000000000 : ℝ) := by
    have hpowers : (193/100000 : ℝ)^8281 ≤ (2065369/195312500000000000 : ℝ)^2048 := by
      have hnat : (193 : ℕ)^8281*195312500000000000^2048 ≤ 2065369^2048*100000^8281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        193 100000 2065369 195312500000000000 8281 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (193/100000 : ℝ)) (X := (2065369/195312500000000000 : ℝ)) (by norm_num) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1401/5000 : ℝ) ^ (8281/2048 : ℝ) ≤ (58325857048643611/10000000000000000000 : ℝ) := by
    have hpowers : (1401/5000 : ℝ)^8281 ≤ (58325857048643611/10000000000000000000 : ℝ)^2048 := by
      have hnat : (1401 : ℕ)^8281*10000000000000000000^2048 ≤ 58325857048643611^2048*5000^8281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1401 5000 58325857048643611 10000000000000000000 8281 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1401/5000 : ℝ)) (X := (58325857048643611/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (97656250002065369/97656250000000000 : ℝ) ≤ (5000000000026153/5000000000000000 : ℝ) ^ (8281/2048 : ℝ) := by
    have hpowers : (97656250002065369/97656250000000000 : ℝ)^2048 ≤ (5000000000026153/5000000000000000 : ℝ)^8281 := by
      have hnat : (97656250002065369 : ℕ)^2048*5000000000000000^8281 ≤ 5000000000026153^8281*97656250000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        97656250002065369 97656250000000000 5000000000026153 5000000000000000 2048 8281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000000026153/5000000000000000 : ℝ)) (X := (97656250002065369/97656250000000000 : ℝ)) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50291629285771952519/50000000000000000000 : ℝ) ≤ (1001439319442289/1000000000000000 : ℝ) ^ (8281/2048 : ℝ) := by
    have hpowers : (50291629285771952519/50000000000000000000 : ℝ)^2048 ≤ (1001439319442289/1000000000000000 : ℝ)^8281 := by
      have hnat : (50291629285771952519 : ℕ)^2048*1000000000000000^8281 ≤ 1001439319442289^8281*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50291629285771952519 50000000000000000000 1001439319442289 1000000000000000 2048 8281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001439319442289/1000000000000000 : ℝ)) (X := (50291629285771952519/50000000000000000000 : ℝ)) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5058325857048643611/5000000000000000000 : ℝ) ≤ (5014393194396737/5000000000000000 : ℝ) ^ (8281/2048 : ℝ) := by
    have hpowers : (5058325857048643611/5000000000000000000 : ℝ)^2048 ≤ (5014393194396737/5000000000000000 : ℝ)^8281 := by
      have hnat : (5058325857048643611 : ℕ)^2048*5000000000000000^8281 ≤ 5014393194396737^8281*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5058325857048643611 5000000000000000000 5014393194396737 5000000000000000 2048 8281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5014393194396737/5000000000000000 : ℝ)) (X := (5058325857048643611/5000000000000000000 : ℝ)) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2065369/195312500000000000 : ℝ) ≤ ((139132222114214236819/139135000000000000000 : ℝ)+2*(1799149296323/347837500000000 : ℝ)*(193/100000 : ℝ))^(8281/2048 : ℝ) := by
    rw [show (139132222114214236819/139135000000000000000 : ℝ)+2*(1799149296323/347837500000000 : ℝ)*(193/100000 : ℝ)=(5000000000026153/5000000000000000 : ℝ) by norm_num, show 1+2*(2065369/195312500000000000 : ℝ)=(97656250002065369/97656250000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(58325857048643611/10000000000000000000 : ℝ)+(2065369/195312500000000000 : ℝ) ≤ ((139132222114214236819/139135000000000000000 : ℝ)+(1799149296323/347837500000000 : ℝ)*((1401/5000 : ℝ)+(193/100000 : ℝ)))^(8281/2048 : ℝ) := by
    rw [show (139132222114214236819/139135000000000000000 : ℝ)+(1799149296323/347837500000000 : ℝ)*((1401/5000 : ℝ)+(193/100000 : ℝ))=(1001439319442289/1000000000000000 : ℝ) by norm_num, show 1+(58325857048643611/10000000000000000000 : ℝ)+(2065369/195312500000000000 : ℝ)=(50291629285771952519/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(58325857048643611/10000000000000000000 : ℝ) ≤ ((139132222114214236819/139135000000000000000 : ℝ)+2*(1799149296323/347837500000000 : ℝ)*(1401/5000 : ℝ))^(8281/2048 : ℝ) := by
    rw [show (139132222114214236819/139135000000000000000 : ℝ)+2*(1799149296323/347837500000000 : ℝ)*(1401/5000 : ℝ)=(5014393194396737/5000000000000000 : ℝ) by norm_num, show 1+2*(58325857048643611/10000000000000000000 : ℝ)=(5058325857048643611/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (139132222114214236819/139135000000000000000 : ℝ)*(X 1 0+X 2 0)+(1799149296323/347837500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8281/2048 : ℝ)) (lo := (193/100000 : ℝ)) (hi := (1401/5000 : ℝ)) (c := (139132222114214236819/139135000000000000000 : ℝ)) (alpha := (1799149296323/347837500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (139132222114214236819/139135000000000000000 : ℝ)*(X 0 1+X 2 1)+(1799149296323/347837500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8281/2048 : ℝ)) (lo := (193/100000 : ℝ)) (hi := (1401/5000 : ℝ)) (c := (139132222114214236819/139135000000000000000 : ℝ)) (alpha := (1799149296323/347837500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (139132222114214236819/139135000000000000000 : ℝ)*(X 0 2+X 1 2)+(1799149296323/347837500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8281/2048 : ℝ)) (lo := (193/100000 : ℝ)) (hi := (1401/5000 : ℝ)) (c := (139132222114214236819/139135000000000000000 : ℝ)) (alpha := (1799149296323/347837500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-529294643/2500000000 : ℝ)*X 0 0+(1143185701/2000000000 : ℝ)*X 0 1+(4990969803/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5422044457/10000000000 : ℝ)*X 1 0+(-501896557/2000000000 : ℝ)*X 1 1+(1247742507/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((677755667/1250000000 : ℝ)*X 2 0+(2495484561/5000000000 : ℝ)*X 2 1+(-2509482787/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1080472219/2500000000 : ℝ)*X 0 0+(114592311/312500000 : ℝ)*X 0 1+(5094260899/10000000000 : ℝ)*X 0 2+(1080472219/2500000000 : ℝ)*X 1 0+(114592311/312500000 : ℝ)*X 1 1+(5094260899/10000000000 : ℝ)*X 1 2+(1080472219/2500000000 : ℝ)*X 2 0+(114592311/312500000 : ℝ)*X 2 1+(5094260899/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-264758197/1250000000 : ℝ)*X 0 0+(1250267573/2500000000 : ℝ)*X 0 1+(2852810901/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1309169731/2500000000 : ℝ)*X 1 0+(-1794828039/10000000000 : ℝ)*X 1 1+(5705624191/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((163646151/312500000 : ℝ)*X 2 0+(5705626543/10000000000 : ℝ)*X 2 1+(-897413787/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((432362993/1000000000 : ℝ)*X 0 0+(5074371679/10000000000 : ℝ)*X 0 1+(3687241157/10000000000 : ℝ)*X 0 2+(432362993/1000000000 : ℝ)*X 1 0+(5074371679/10000000000 : ℝ)*X 1 1+(3687241157/10000000000 : ℝ)*X 1 2+(432362993/1000000000 : ℝ)*X 2 0+(5074371679/10000000000 : ℝ)*X 2 1+(3687241157/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((3925601/5000000000 : ℝ)*X 0 0+(5489937633/10000000000 : ℝ)*X 0 1+(6368397567/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((193755881/2000000000 : ℝ)*X 1 0+(-4443960703/10000000000 : ℝ)*X 1 1+(6931776193/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((968772399/10000000000 : ℝ)*X 2 0+(6931760797/10000000000 : ℝ)*X 2 1+(-4443982767/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1922292943/10000000000 : ℝ)*X 0 0+(291244811/500000000 : ℝ)*X 0 1+(1255354621/2500000000 : ℝ)*X 0 2+(1922292943/10000000000 : ℝ)*X 1 0+(291244811/500000000 : ℝ)*X 1 1+(1255354621/2500000000 : ℝ)*X 1 2+(1922292943/10000000000 : ℝ)*X 2 0+(291244811/500000000 : ℝ)*X 2 1+(1255354621/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (96151757670978516709900182483/6956750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1040009025564473/100000000000000 : ℝ)*(major0) + (1040009025564473/100000000000000 : ℝ)*(major1) + (1040009025564473/100000000000000 : ℝ)*(major2) + (689695946860027/50000000000000 : ℝ)*(sp0) + (86212039383117/6250000000000 : ℝ)*(sp1) + (86211969939297/6250000000000 : ℝ)*(sp2) + (350310493871617/50000000000000 : ℝ)*(sp3) + (908353213/50000000000000 : ℝ)*(sp4) + (144993497/10000000000000 : ℝ)*(sp5) + (2325202739/100000000000000 : ℝ)*(sp6) + (593866729/50000000000000 : ℝ)*(sp8) + (163619019/20000000000000 : ℝ)*(sp9) + (1053928447/100000000000000 : ℝ)*(sp10) + (1704513711/100000000000000 : ℝ)*(sp11) + (43788918266059/6250000000000 : ℝ)*(f.failure) + (689697449079969/50000000000000 : ℝ)*(f.sum) + (67736669964483/139135000000000000000000000000 : ℝ)*base66 + (147968765407927468613/13913500000000000000000000000000000 : ℝ)*base68 + (158198992220578468613/13913500000000000000000000000000000 : ℝ)*base70 + (74308233050579468613/13913500000000000000000000000000000 : ℝ)*base72 + (467604446751923/139135000000000000000000000000 : ℝ)*base74 + (63574438007311968613/13913500000000000000000000000000000 : ℝ)*base76 + (94141476697968468613/13913500000000000000000000000000000 : ℝ)*base78 + (166951352831031468613/13913500000000000000000000000000000 : ℝ)*base80 + (106472260516953/139135000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1764411/625000000000000000000 : ℝ)*base90 + (1764411/625000000000000000000 : ℝ)*base92 + (1764411/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43910605862466783640452942327/6956750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (107093099/100000000000000 : ℝ)*(lower4) + (1070127945229637/100000000000000 : ℝ)*(major0) + (1070127945229637/100000000000000 : ℝ)*(major1) + (1070127945229637/100000000000000 : ℝ)*(major2) + (523542819/50000000000000 : ℝ)*(sp0) + (2815063109/100000000000000 : ℝ)*(sp1) + (2959770691/50000000000000 : ℝ)*(sp2) + (354834487605831/25000000000000 : ℝ)*(sp4) + (283867931124103/20000000000000 : ℝ)*(sp5) + (354834215274103/25000000000000 : ℝ)*(sp6) + (360455572458547/50000000000000 : ℝ)*(sp7) + (14777847/390625000000 : ℝ)*(sp8) + (30995417/10000000000000 : ℝ)*(sp9) + (877253149/50000000000000 : ℝ)*(sp11) + (720912899423391/100000000000000 : ℝ)*(f.failure) + (709671390318897/50000000000000 : ℝ)*(f.sum) + (222484920069689/69567500000000000000000000000 : ℝ)*base65 + (78259465260784195297/13913500000000000000000000000000000 : ℝ)*base68 + (72378090454940195297/13913500000000000000000000000000000 : ℝ)*base70 + (33803037775163695297/13913500000000000000000000000000000 : ℝ)*base72 + (324538474668251/69567500000000000000000000000 : ℝ)*base74 + (39839969907673695297/13913500000000000000000000000000000 : ℝ)*base76 + (71088290555639195297/13913500000000000000000000000000000 : ℝ)*base78 + (94506730405375195297/13913500000000000000000000000000000 : ℝ)*base80 + (115161592256543/34783750000000000000000000000 : ℝ)*base82 + (26864639/10000000000000000000000 : ℝ)*base90 + (26864639/10000000000000000000000 : ℝ)*base92 + (26864639/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1089_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148440671/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1401/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (193/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5347/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10341/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1089_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1089_s2_0 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-135832159/625000000 : ℝ)*x 0 + (86268839/156250000 : ℝ)*x 1 + (206002109/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135832159/625000000 : ℝ)^4141 ≤ (6581477951737/50000000000000 : ℝ)^3117 := by
    have hnat : (135832159 : ℕ)^4141*50000000000000^3117 ≤ 6581477951737^3117*625000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135832159 625000000 6581477951737 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86268839/156250000 : ℝ)^4141 ≤ (2839008344313/6250000000000 : ℝ)^3117 := by
    have hnat : (86268839 : ℕ)^4141*6250000000000^3117 ≤ 2839008344313^3117*156250000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86268839 156250000 2839008344313 6250000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (206002109/400000000 : ℝ)^4141 ≤ (20706455291139/50000000000000 : ℝ)^3117 := by
    have hnat : (206002109 : ℕ)^4141*50000000000000^3117 ≤ 20706455291139^3117*400000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206002109 400000000 20706455291139 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-135832159/625000000 : ℝ), (86268839/156250000 : ℝ), (206002109/400000000 : ℝ)] ![(6581477951737/50000000000000 : ℝ), (2839008344313/6250000000000 : ℝ), (20706455291139/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-135832159/625000000 : ℝ)|^4141 ≤ (6581477951737/50000000000000 : ℝ)^3117
        have hw : |(-135832159/625000000 : ℝ)|=(135832159/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(86268839/156250000 : ℝ)|^4141 ≤ (2839008344313/6250000000000 : ℝ)^3117
        have hw : |(86268839/156250000 : ℝ)|=(86268839/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(206002109/400000000 : ℝ)|^4141 ≤ (20706455291139/50000000000000 : ℝ)^3117
        have hw : |(206002109/400000000 : ℝ)|=(206002109/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s2_1 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1344044527/2500000000 : ℝ)*x 0 + (-295836197/1250000000 : ℝ)*x 1 + (128751333/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344044527/2500000000 : ℝ)^4141 ≤ (21922929236443/50000000000000 : ℝ)^3117 := by
    have hnat : (1344044527 : ℕ)^4141*50000000000000^3117 ≤ 21922929236443^3117*2500000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344044527 2500000000 21922929236443 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (295836197/1250000000 : ℝ)^4141 ≤ (7370612290259/50000000000000 : ℝ)^3117 := by
    have hnat : (295836197 : ℕ)^4141*50000000000000^3117 ≤ 7370612290259^3117*1250000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      295836197 1250000000 7370612290259 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128751333/250000000 : ℝ)^4141 ≤ (10353229234663/25000000000000 : ℝ)^3117 := by
    have hnat : (128751333 : ℕ)^4141*25000000000000^3117 ≤ 10353229234663^3117*250000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128751333 250000000 10353229234663 25000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344044527/2500000000 : ℝ), (-295836197/1250000000 : ℝ), (128751333/250000000 : ℝ)] ![(21922929236443/50000000000000 : ℝ), (7370612290259/50000000000000 : ℝ), (10353229234663/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344044527/2500000000 : ℝ)|^4141 ≤ (21922929236443/50000000000000 : ℝ)^3117
        have hw : |(1344044527/2500000000 : ℝ)|=(1344044527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-295836197/1250000000 : ℝ)|^4141 ≤ (7370612290259/50000000000000 : ℝ)^3117
        have hw : |(-295836197/1250000000 : ℝ)|=(295836197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(128751333/250000000 : ℝ)|^4141 ≤ (10353229234663/25000000000000 : ℝ)^3117
        have hw : |(128751333/250000000 : ℝ)|=(128751333/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s2_2 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1344044557/2500000000 : ℝ)*x 0 + (5150053181/10000000000 : ℝ)*x 1 + (-1183344799/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1344044557/2500000000 : ℝ)^4141 ≤ (4384585977307/10000000000000 : ℝ)^3117 := by
    have hnat : (1344044557 : ℕ)^4141*10000000000000^3117 ≤ 4384585977307^3117*2500000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1344044557 2500000000 4384585977307 10000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5150053181/10000000000 : ℝ)^4141 ≤ (20706457726859/50000000000000 : ℝ)^3117 := by
    have hnat : (5150053181 : ℕ)^4141*50000000000000^3117 ≤ 20706457726859^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5150053181 10000000000 20706457726859 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1183344799/5000000000 : ℝ)^4141 ≤ (2948244952513/20000000000000 : ℝ)^3117 := by
    have hnat : (1183344799 : ℕ)^4141*20000000000000^3117 ≤ 2948244952513^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1183344799 5000000000 2948244952513 20000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1344044557/2500000000 : ℝ), (5150053181/10000000000 : ℝ), (-1183344799/5000000000 : ℝ)] ![(4384585977307/10000000000000 : ℝ), (20706457726859/50000000000000 : ℝ), (2948244952513/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1344044557/2500000000 : ℝ)|^4141 ≤ (4384585977307/10000000000000 : ℝ)^3117
        have hw : |(1344044557/2500000000 : ℝ)|=(1344044557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5150053181/10000000000 : ℝ)|^4141 ≤ (20706457726859/50000000000000 : ℝ)^3117
        have hw : |(5150053181/10000000000 : ℝ)|=(5150053181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1183344799/5000000000 : ℝ)|^4141 ≤ (2948244952513/20000000000000 : ℝ)^3117
        have hw : |(-1183344799/5000000000 : ℝ)|=(1183344799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s2_3 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4360256877/10000000000 : ℝ)*x 0 + (4010247277/10000000000 : ℝ)*x 1 + (4740976887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360256877/10000000000 : ℝ)^4141 ≤ (8298970600127/25000000000000 : ℝ)^3117 := by
    have hnat : (4360256877 : ℕ)^4141*25000000000000^3117 ≤ 8298970600127^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360256877 10000000000 8298970600127 25000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4010247277/10000000000 : ℝ)^4141 ≤ (3712911095967/12500000000000 : ℝ)^3117 := by
    have hnat : (4010247277 : ℕ)^4141*12500000000000^3117 ≤ 3712911095967^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4010247277 10000000000 3712911095967 12500000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4740976887/10000000000 : ℝ)^4141 ≤ (18550414406357/50000000000000 : ℝ)^3117 := by
    have hnat : (4740976887 : ℕ)^4141*50000000000000^3117 ≤ 18550414406357^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4740976887 10000000000 18550414406357 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360256877/10000000000 : ℝ), (4010247277/10000000000 : ℝ), (4740976887/10000000000 : ℝ)] ![(8298970600127/25000000000000 : ℝ), (3712911095967/12500000000000 : ℝ), (18550414406357/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360256877/10000000000 : ℝ)|^4141 ≤ (8298970600127/25000000000000 : ℝ)^3117
        have hw : |(4360256877/10000000000 : ℝ)|=(4360256877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4010247277/10000000000 : ℝ)|^4141 ≤ (3712911095967/12500000000000 : ℝ)^3117
        have hw : |(4010247277/10000000000 : ℝ)|=(4010247277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4740976887/10000000000 : ℝ)|^4141 ≤ (18550414406357/50000000000000 : ℝ)^3117
        have hw : |(4740976887/10000000000 : ℝ)|=(4740976887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s2_4 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-271679111/1250000000 : ℝ)*x 0 + (5152709211/10000000000 : ℝ)*x 1 + (1103704339/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271679111/1250000000 : ℝ)^4141 ≤ (263278163/2000000000 : ℝ)^3117 := by
    have hnat : (271679111 : ℕ)^4141*2000000000^3117 ≤ 263278163^3117*1250000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271679111 1250000000 263278163 2000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5152709211/10000000000 : ℝ)^4141 ≤ (20720646089681/50000000000000 : ℝ)^3117 := by
    have hnat : (5152709211 : ℕ)^4141*50000000000000^3117 ≤ 20720646089681^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152709211 10000000000 20720646089681 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103704339/2000000000 : ℝ)^4141 ≤ (9078959930791/20000000000000 : ℝ)^3117 := by
    have hnat : (1103704339 : ℕ)^4141*20000000000000^3117 ≤ 9078959930791^3117*2000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103704339 2000000000 9078959930791 20000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-271679111/1250000000 : ℝ), (5152709211/10000000000 : ℝ), (1103704339/2000000000 : ℝ)] ![(263278163/2000000000 : ℝ), (20720646089681/50000000000000 : ℝ), (9078959930791/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-271679111/1250000000 : ℝ)|^4141 ≤ (263278163/2000000000 : ℝ)^3117
        have hw : |(-271679111/1250000000 : ℝ)|=(271679111/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5152709211/10000000000 : ℝ)|^4141 ≤ (20720646089681/50000000000000 : ℝ)^3117
        have hw : |(5152709211/10000000000 : ℝ)|=(5152709211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1103704339/2000000000 : ℝ)|^4141 ≤ (9078959930791/20000000000000 : ℝ)^3117
        have hw : |(1103704339/2000000000 : ℝ)|=(1103704339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s2_5 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5282344951/10000000000 : ℝ)*x 0 + (-79928843/400000000 : ℝ)*x 1 + (2759260893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5282344951/10000000000 : ℝ)^4141 ≤ (42832115408999/100000000000000 : ℝ)^3117 := by
    have hnat : (5282344951 : ℕ)^4141*100000000000000^3117 ≤ 42832115408999^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282344951 10000000000 42832115408999 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (79928843/400000000 : ℝ)^4141 ≤ (5886541967157/50000000000000 : ℝ)^3117 := by
    have hnat : (79928843 : ℕ)^4141*50000000000000^3117 ≤ 5886541967157^3117*400000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79928843 400000000 5886541967157 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2759260893/5000000000 : ℝ)^4141 ≤ (11348700162107/25000000000000 : ℝ)^3117 := by
    have hnat : (2759260893 : ℕ)^4141*25000000000000^3117 ≤ 11348700162107^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759260893 5000000000 11348700162107 25000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5282344951/10000000000 : ℝ), (-79928843/400000000 : ℝ), (2759260893/5000000000 : ℝ)] ![(42832115408999/100000000000000 : ℝ), (5886541967157/50000000000000 : ℝ), (11348700162107/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5282344951/10000000000 : ℝ)|^4141 ≤ (42832115408999/100000000000000 : ℝ)^3117
        have hw : |(5282344951/10000000000 : ℝ)|=(5282344951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-79928843/400000000 : ℝ)|^4141 ≤ (5886541967157/50000000000000 : ℝ)^3117
        have hw : |(-79928843/400000000 : ℝ)|=(79928843/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2759260893/5000000000 : ℝ)|^4141 ≤ (11348700162107/25000000000000 : ℝ)^3117
        have hw : |(2759260893/5000000000 : ℝ)|=(2759260893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s2_6 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1056469029/2000000000 : ℝ)*x 0 + (5518521701/10000000000 : ℝ)*x 1 + (-999110463/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1056469029/2000000000 : ℝ)^4141 ≤ (42832117498839/100000000000000 : ℝ)^3117 := by
    have hnat : (1056469029 : ℕ)^4141*100000000000000^3117 ≤ 42832117498839^3117*2000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056469029 2000000000 42832117498839 100000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5518521701/10000000000 : ℝ)^4141 ≤ (11348699929881/25000000000000 : ℝ)^3117 := by
    have hnat : (5518521701 : ℕ)^4141*25000000000000^3117 ≤ 11348699929881^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518521701 10000000000 11348699929881 25000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (999110463/5000000000 : ℝ)^4141 ≤ (5886541384019/50000000000000 : ℝ)^3117 := by
    have hnat : (999110463 : ℕ)^4141*50000000000000^3117 ≤ 5886541384019^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999110463 5000000000 5886541384019 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1056469029/2000000000 : ℝ), (5518521701/10000000000 : ℝ), (-999110463/5000000000 : ℝ)] ![(42832117498839/100000000000000 : ℝ), (11348699929881/25000000000000 : ℝ), (5886541384019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1056469029/2000000000 : ℝ)|^4141 ≤ (42832117498839/100000000000000 : ℝ)^3117
        have hw : |(1056469029/2000000000 : ℝ)|=(1056469029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5518521701/10000000000 : ℝ)|^4141 ≤ (11348699929881/25000000000000 : ℝ)^3117
        have hw : |(5518521701/10000000000 : ℝ)|=(5518521701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-999110463/5000000000 : ℝ)|^4141 ≤ (5886541384019/50000000000000 : ℝ)^3117
        have hw : |(-999110463/5000000000 : ℝ)|=(999110463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1089_s2_7 (p : ℝ) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4360490119/10000000000 : ℝ)*x 0 + (1183936859/2500000000 : ℝ)*x 1 + (2007765233/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360490119/10000000000 : ℝ)^4141 ≤ (16599120763269/50000000000000 : ℝ)^3117 := by
    have hnat : (4360490119 : ℕ)^4141*50000000000000^3117 ≤ 16599120763269^3117*10000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360490119 10000000000 16599120763269 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1183936859/2500000000 : ℝ)^4141 ≤ (3704647104847/10000000000000 : ℝ)^3117 := by
    have hnat : (1183936859 : ℕ)^4141*10000000000000^3117 ≤ 3704647104847^3117*2500000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1183936859 2500000000 3704647104847 10000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2007765233/5000000000 : ℝ)^4141 ≤ (14877643699017/50000000000000 : ℝ)^3117 := by
    have hnat : (2007765233 : ℕ)^4141*50000000000000^3117 ≤ 14877643699017^3117*5000000000^4141 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007765233 5000000000 14877643699017 50000000000000 4141 3117 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4141/1024 : ℝ)) 4141 3117 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360490119/10000000000 : ℝ), (1183936859/2500000000 : ℝ), (2007765233/5000000000 : ℝ)] ![(16599120763269/50000000000000 : ℝ), (3704647104847/10000000000000 : ℝ), (14877643699017/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360490119/10000000000 : ℝ)|^4141 ≤ (16599120763269/50000000000000 : ℝ)^3117
        have hw : |(4360490119/10000000000 : ℝ)|=(4360490119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1183936859/2500000000 : ℝ)|^4141 ≤ (3704647104847/10000000000000 : ℝ)^3117
        have hw : |(1183936859/2500000000 : ℝ)|=(1183936859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2007765233/5000000000 : ℝ)|^4141 ≤ (14877643699017/50000000000000 : ℝ)^3117
        have hw : |(2007765233/5000000000 : ℝ)|=(2007765233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1089_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148440671/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10341/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (8823/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8333/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10341/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5347/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10341/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5347/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10341/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5347/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10341/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5347/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10341/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5347/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10341/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5347/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5347/100000 : ℝ) ^ (8281/2048 : ℝ) ≤ (719727639214179/100000000000000000000 : ℝ) := by
    have hpowers : (5347/100000 : ℝ)^8281 ≤ (719727639214179/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5347 : ℕ)^8281*100000000000000000000^2048 ≤ 719727639214179^2048*100000^8281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5347 100000 719727639214179 100000000000000000000 8281 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5347/100000 : ℝ)) (X := (719727639214179/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (10341/50000 : ℝ) ^ (8281/2048 : ℝ) ≤ (170855049472179817/100000000000000000000 : ℝ) := by
    have hpowers : (10341/50000 : ℝ)^8281 ≤ (170855049472179817/100000000000000000000 : ℝ)^2048 := by
      have hnat : (10341 : ℕ)^8281*100000000000000000000^2048 ≤ 170855049472179817^2048*50000^8281 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10341 50000 170855049472179817 100000000000000000000 8281 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10341/50000 : ℝ)) (X := (170855049472179817/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000719727639214179/50000000000000000000 : ℝ) ≤ (400001423977027/400000000000000 : ℝ) ^ (8281/2048 : ℝ) := by
    have hpowers : (50000719727639214179/50000000000000000000 : ℝ)^2048 ≤ (400001423977027/400000000000000 : ℝ)^8281 := by
      have hnat : (50000719727639214179 : ℕ)^2048*400000000000000^8281 ≤ 400001423977027^8281*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000719727639214179 50000000000000000000 400001423977027 400000000000000 2048 8281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400001423977027/400000000000000 : ℝ)) (X := (50000719727639214179/50000000000000000000 : ℝ)) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25042893694277848499/25000000000000000000 : ℝ) ≤ (400169621290977/400000000000000 : ℝ) ^ (8281/2048 : ℝ) := by
    have hpowers : (25042893694277848499/25000000000000000000 : ℝ)^2048 ≤ (400169621290977/400000000000000 : ℝ)^8281 := by
      have hnat : (25042893694277848499 : ℕ)^2048*400000000000000^8281 ≤ 400169621290977^8281*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25042893694277848499 25000000000000000000 400169621290977 400000000000000 2048 8281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400169621290977/400000000000000 : ℝ)) (X := (25042893694277848499/25000000000000000000 : ℝ)) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50170855049472179817/50000000000000000000 : ℝ) ≤ (400337818604927/400000000000000 : ℝ) ^ (8281/2048 : ℝ) := by
    have hpowers : (50170855049472179817/50000000000000000000 : ℝ)^2048 ≤ (400337818604927/400000000000000 : ℝ)^8281 := by
      have hnat : (50170855049472179817 : ℕ)^2048*400000000000000^8281 ≤ 400337818604927^8281*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50170855049472179817 50000000000000000000 400337818604927 400000000000000 2048 8281 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400337818604927/400000000000000 : ℝ)) (X := (50170855049472179817/50000000000000000000 : ℝ)) (by norm_num) 8281 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(719727639214179/100000000000000000000 : ℝ) ≤ ((1226444626922465549/1226800000000000000 : ℝ)+2*(3363946279/1226800000000 : ℝ)*(5347/100000 : ℝ))^(8281/2048 : ℝ) := by
    rw [show (1226444626922465549/1226800000000000000 : ℝ)+2*(3363946279/1226800000000 : ℝ)*(5347/100000 : ℝ)=(400001423977027/400000000000000 : ℝ) by norm_num, show 1+2*(719727639214179/100000000000000000000 : ℝ)=(50000719727639214179/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(170855049472179817/100000000000000000000 : ℝ)+(719727639214179/100000000000000000000 : ℝ) ≤ ((1226444626922465549/1226800000000000000 : ℝ)+(3363946279/1226800000000 : ℝ)*((10341/50000 : ℝ)+(5347/100000 : ℝ)))^(8281/2048 : ℝ) := by
    rw [show (1226444626922465549/1226800000000000000 : ℝ)+(3363946279/1226800000000 : ℝ)*((10341/50000 : ℝ)+(5347/100000 : ℝ))=(400169621290977/400000000000000 : ℝ) by norm_num, show 1+(170855049472179817/100000000000000000000 : ℝ)+(719727639214179/100000000000000000000 : ℝ)=(25042893694277848499/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(170855049472179817/100000000000000000000 : ℝ) ≤ ((1226444626922465549/1226800000000000000 : ℝ)+2*(3363946279/1226800000000 : ℝ)*(10341/50000 : ℝ))^(8281/2048 : ℝ) := by
    rw [show (1226444626922465549/1226800000000000000 : ℝ)+2*(3363946279/1226800000000 : ℝ)*(10341/50000 : ℝ)=(400337818604927/400000000000000 : ℝ) by norm_num, show 1+2*(170855049472179817/100000000000000000000 : ℝ)=(50170855049472179817/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1226444626922465549/1226800000000000000 : ℝ)*(X 1 0+X 2 0)+(3363946279/1226800000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8281/2048 : ℝ)) (lo := (5347/100000 : ℝ)) (hi := (10341/50000 : ℝ)) (c := (1226444626922465549/1226800000000000000 : ℝ)) (alpha := (3363946279/1226800000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1226444626922465549/1226800000000000000 : ℝ)*(X 0 1+X 2 1)+(3363946279/1226800000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8281/2048 : ℝ)) (lo := (5347/100000 : ℝ)) (hi := (10341/50000 : ℝ)) (c := (1226444626922465549/1226800000000000000 : ℝ)) (alpha := (3363946279/1226800000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1226444626922465549/1226800000000000000 : ℝ)*(X 0 2+X 1 2)+(3363946279/1226800000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8281/2048 : ℝ)) (lo := (5347/100000 : ℝ)) (hi := (10341/50000 : ℝ)) (c := (1226444626922465549/1226800000000000000 : ℝ)) (alpha := (3363946279/1226800000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-135832159/625000000 : ℝ)*X 0 0+(86268839/156250000 : ℝ)*X 0 1+(206002109/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1344044527/2500000000 : ℝ)*X 1 0+(-295836197/1250000000 : ℝ)*X 1 1+(128751333/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1344044557/2500000000 : ℝ)*X 2 0+(5150053181/10000000000 : ℝ)*X 2 1+(-1183344799/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4360256877/10000000000 : ℝ)*X 0 0+(4010247277/10000000000 : ℝ)*X 0 1+(4740976887/10000000000 : ℝ)*X 0 2+(4360256877/10000000000 : ℝ)*X 1 0+(4010247277/10000000000 : ℝ)*X 1 1+(4740976887/10000000000 : ℝ)*X 1 2+(4360256877/10000000000 : ℝ)*X 2 0+(4010247277/10000000000 : ℝ)*X 2 1+(4740976887/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-271679111/1250000000 : ℝ)*X 0 0+(5152709211/10000000000 : ℝ)*X 0 1+(1103704339/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5282344951/10000000000 : ℝ)*X 1 0+(-79928843/400000000 : ℝ)*X 1 1+(2759260893/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1056469029/2000000000 : ℝ)*X 2 0+(5518521701/10000000000 : ℝ)*X 2 1+(-999110463/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4360490119/10000000000 : ℝ)*X 0 0+(1183936859/2500000000 : ℝ)*X 0 1+(2007765233/5000000000 : ℝ)*X 0 2+(4360490119/10000000000 : ℝ)*X 1 0+(1183936859/2500000000 : ℝ)*X 1 1+(2007765233/5000000000 : ℝ)*X 1 2+(4360490119/10000000000 : ℝ)*X 2 0+(1183936859/2500000000 : ℝ)*X 2 1+(2007765233/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1089_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12355612387521533980280967/1533500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (357742483/25000000000000 : ℝ)*(base19) + (1457799843/100000000000000 : ℝ)*(base23) + (17907873/100000000000000 : ℝ)*(lower2) + (6664963/4000000000000 : ℝ)*(upper3) + (137552223/100000000000000 : ℝ)*(upper5) + (101571402151061/5000000000000 : ℝ)*(major0) + (101571402151061/5000000000000 : ℝ)*(major1) + (101571402151061/5000000000000 : ℝ)*(major2) + (2694325391161443/100000000000000 : ℝ)*(sp0) + (1347171311983097/50000000000000 : ℝ)*(sp1) + (2694342597136283/100000000000000 : ℝ)*(sp2) + (136850324295291/10000000000000 : ℝ)*(sp3) + (18663774683/100000000000000 : ℝ)*(sp4) + (8519582319/100000000000000 : ℝ)*(sp7) + (342127940633807/25000000000000 : ℝ)*(f.failure) + (1347172027468063/50000000000000 : ℝ)*(f.sum) + (863510628769/613400000000000000000000000 : ℝ)*base66 + (23465122839567489/6134000000000000000000000000000 : ℝ)*base67 + (20850923744358511/6134000000000000000000000000000 : ℝ)*base70 + (38649321576424511/6134000000000000000000000000000 : ℝ)*base72 + (671643978953/306700000000000000000000000 : ℝ)*base73 + (19704689049838511/6134000000000000000000000000000 : ℝ)*base76 + (47841522795072511/6134000000000000000000000000000 : ℝ)*base78 + (22446528611220511/6134000000000000000000000000000 : ℝ)*base80 + (944242136953/306700000000000000000000000 : ℝ)*base82 + (23635503/2500000000000000000000 : ℝ)*base90 + (23635503/2500000000000000000000 : ℝ)*base92 + (23635503/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (106026510514739589061289793/30670000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8434573/1250000000000 : ℝ)*(base19) + (425494509/50000000000000 : ℝ)*(base23) + (56646951/50000000000000 : ℝ)*(upper3) + (8999327/50000000000000 : ℝ)*(lower4) + (59711181/100000000000000 : ℝ)*(upper5) + (1030527888740519/50000000000000 : ℝ)*(major0) + (1030527888740519/50000000000000 : ℝ)*(major1) + (1030527888740519/50000000000000 : ℝ)*(major2) + (2903600791/50000000000000 : ℝ)*(sp1) + (326310099/4000000000000 : ℝ)*(sp2) + (273364036667521/10000000000000 : ℝ)*(sp4) + (683408471176947/25000000000000 : ℝ)*(sp5) + (1366815678966859/50000000000000 : ℝ)*(sp6) + (694235536526589/50000000000000 : ℝ)*(sp7) + (694235536526589/50000000000000 : ℝ)*(f.failure) + (273364036667521/10000000000000 : ℝ)*(f.sum) + (9152691290033/1533500000000000000000000000 : ℝ)*base65 + (285535837131240069/61340000000000000000000000000000 : ℝ)*base68 + (36542654155559931/61340000000000000000000000000000 : ℝ)*base69 + (114831415828039931/61340000000000000000000000000000 : ℝ)*base71 + (312040095451/383375000000000000000000000 : ℝ)*base73 + (344166549806160069/61340000000000000000000000000000 : ℝ)*base76 + (135047389474400069/61340000000000000000000000000000 : ℝ)*base78 + (467999517608460069/61340000000000000000000000000000 : ℝ)*base80 + (1332138082709/306700000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (19498781/5000000000000000000000 : ℝ)*base90 + (19498781/5000000000000000000000 : ℝ)*base92 + (19498781/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1089_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148440671/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10341/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5347/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8823/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8333/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1089_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1089_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148440671/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8823/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8333/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1089_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1089_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1089_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8281/2048 : ℝ) ≤ p) (hpb : p ≤ (4141/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148440671/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8823/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8333/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1089_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
