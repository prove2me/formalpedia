-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1436_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:55:54.552814+00:00
-- url     : https://prove2.me/submissions/4a53edbc-24d0-4cad-9b8c-ed00952bf361

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
theorem support_rectangle_w1436_s6_0 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1965464227/10000000000 : ℝ)*x 0 + (1351964971/2500000000 : ℝ)*x 1 + (5247059521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1965464227/10000000000 : ℝ)^1099 ≤ (2998102831917/25000000000000 : ℝ)^843 := by
    have hnat : (1965464227 : ℕ)^1099*25000000000000^843 ≤ 2998102831917^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1965464227 10000000000 2998102831917 25000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351964971/2500000000 : ℝ)^1099 ≤ (22434753760003/50000000000000 : ℝ)^843 := by
    have hnat : (1351964971 : ℕ)^1099*50000000000000^843 ≤ 22434753760003^843*2500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351964971 2500000000 22434753760003 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247059521/10000000000 : ℝ)^1099 ≤ (43138081143249/100000000000000 : ℝ)^843 := by
    have hnat : (5247059521 : ℕ)^1099*100000000000000^843 ≤ 43138081143249^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247059521 10000000000 43138081143249 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1965464227/10000000000 : ℝ), (1351964971/2500000000 : ℝ), (5247059521/10000000000 : ℝ)] ![(2998102831917/25000000000000 : ℝ), (22434753760003/50000000000000 : ℝ), (43138081143249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1965464227/10000000000 : ℝ)|^1099 ≤ (2998102831917/25000000000000 : ℝ)^843
        have hw : |(-1965464227/10000000000 : ℝ)|=(1965464227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351964971/2500000000 : ℝ)|^1099 ≤ (22434753760003/50000000000000 : ℝ)^843
        have hw : |(1351964971/2500000000 : ℝ)|=(1351964971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247059521/10000000000 : ℝ)|^1099 ≤ (43138081143249/100000000000000 : ℝ)^843
        have hw : |(5247059521/10000000000 : ℝ)|=(5247059521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s6_1 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2673589757/5000000000 : ℝ)*x 0 + (-1023662731/5000000000 : ℝ)*x 1 + (5247059521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673589757/5000000000 : ℝ)^1099 ≤ (1768570621751/4000000000000 : ℝ)^843 := by
    have hnat : (2673589757 : ℕ)^1099*4000000000000^843 ≤ 1768570621751^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673589757 5000000000 1768570621751 4000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1023662731/5000000000 : ℝ)^1099 ≤ (316191332417/2500000000000 : ℝ)^843 := by
    have hnat : (1023662731 : ℕ)^1099*2500000000000^843 ≤ 316191332417^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023662731 5000000000 316191332417 2500000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247059521/10000000000 : ℝ)^1099 ≤ (43138081143249/100000000000000 : ℝ)^843 := by
    have hnat : (5247059521 : ℕ)^1099*100000000000000^843 ≤ 43138081143249^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247059521 10000000000 43138081143249 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673589757/5000000000 : ℝ), (-1023662731/5000000000 : ℝ), (5247059521/10000000000 : ℝ)] ![(1768570621751/4000000000000 : ℝ), (316191332417/2500000000000 : ℝ), (43138081143249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673589757/5000000000 : ℝ)|^1099 ≤ (1768570621751/4000000000000 : ℝ)^843
        have hw : |(2673589757/5000000000 : ℝ)|=(2673589757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1023662731/5000000000 : ℝ)|^1099 ≤ (316191332417/2500000000000 : ℝ)^843
        have hw : |(-1023662731/5000000000 : ℝ)|=(1023662731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247059521/10000000000 : ℝ)|^1099 ≤ (43138081143249/100000000000000 : ℝ)^843
        have hw : |(5247059521/10000000000 : ℝ)|=(5247059521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s6_2 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2673589757/5000000000 : ℝ)*x 0 + (5247059521/10000000000 : ℝ)*x 1 + (-1023662731/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673589757/5000000000 : ℝ)^1099 ≤ (1768570621751/4000000000000 : ℝ)^843 := by
    have hnat : (2673589757 : ℕ)^1099*4000000000000^843 ≤ 1768570621751^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673589757 5000000000 1768570621751 4000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247059521/10000000000 : ℝ)^1099 ≤ (43138081143249/100000000000000 : ℝ)^843 := by
    have hnat : (5247059521 : ℕ)^1099*100000000000000^843 ≤ 43138081143249^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247059521 10000000000 43138081143249 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1023662731/5000000000 : ℝ)^1099 ≤ (316191332417/2500000000000 : ℝ)^843 := by
    have hnat : (1023662731 : ℕ)^1099*2500000000000^843 ≤ 316191332417^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023662731 5000000000 316191332417 2500000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673589757/5000000000 : ℝ), (5247059521/10000000000 : ℝ), (-1023662731/5000000000 : ℝ)] ![(1768570621751/4000000000000 : ℝ), (43138081143249/100000000000000 : ℝ), (316191332417/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673589757/5000000000 : ℝ)|^1099 ≤ (1768570621751/4000000000000 : ℝ)^843
        have hw : |(2673589757/5000000000 : ℝ)|=(2673589757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247059521/10000000000 : ℝ)|^1099 ≤ (43138081143249/100000000000000 : ℝ)^843
        have hw : |(5247059521/10000000000 : ℝ)|=(5247059521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1023662731/5000000000 : ℝ)|^1099 ≤ (316191332417/2500000000000 : ℝ)^843
        have hw : |(-1023662731/5000000000 : ℝ)|=(1023662731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s6_3 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (860525181/2000000000 : ℝ)*x 0 + (413141609/1000000000 : ℝ)*x 1 + (1120043357/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (860525181/2000000000 : ℝ)^1099 ≤ (2081549745037/6250000000000 : ℝ)^843 := by
    have hnat : (860525181 : ℕ)^1099*6250000000000^843 ≤ 2081549745037^843*2000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860525181 2000000000 2081549745037 6250000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (413141609/1000000000 : ℝ)^1099 ≤ (31587618320853/100000000000000 : ℝ)^843 := by
    have hnat : (413141609 : ℕ)^1099*100000000000000^843 ≤ 31587618320853^843*1000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      413141609 1000000000 31587618320853 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1120043357/2500000000 : ℝ)^1099 ≤ (1097112054517/3125000000000 : ℝ)^843 := by
    have hnat : (1120043357 : ℕ)^1099*3125000000000^843 ≤ 1097112054517^843*2500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120043357 2500000000 1097112054517 3125000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(860525181/2000000000 : ℝ), (413141609/1000000000 : ℝ), (1120043357/2500000000 : ℝ)] ![(2081549745037/6250000000000 : ℝ), (31587618320853/100000000000000 : ℝ), (1097112054517/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(860525181/2000000000 : ℝ)|^1099 ≤ (2081549745037/6250000000000 : ℝ)^843
        have hw : |(860525181/2000000000 : ℝ)|=(860525181/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(413141609/1000000000 : ℝ)|^1099 ≤ (31587618320853/100000000000000 : ℝ)^843
        have hw : |(413141609/1000000000 : ℝ)|=(413141609/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1120043357/2500000000 : ℝ)|^1099 ≤ (1097112054517/3125000000000 : ℝ)^843
        have hw : |(1120043357/2500000000 : ℝ)|=(1120043357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s6_4 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-61421101/312500000 : ℝ)*x 0 + (5247640023/10000000000 : ℝ)*x 1 + (2703638283/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (61421101/312500000 : ℝ)^1099 ≤ (5996249433367/50000000000000 : ℝ)^843 := by
    have hnat : (61421101 : ℕ)^1099*50000000000000^843 ≤ 5996249433367^843*312500000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61421101 312500000 5996249433367 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247640023/10000000000 : ℝ)^1099 ≤ (21572151542677/50000000000000 : ℝ)^843 := by
    have hnat : (5247640023 : ℕ)^1099*50000000000000^843 ≤ 21572151542677^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247640023 10000000000 21572151542677 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703638283/5000000000 : ℝ)^1099 ≤ (44863198030027/100000000000000 : ℝ)^843 := by
    have hnat : (2703638283 : ℕ)^1099*100000000000000^843 ≤ 44863198030027^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703638283 5000000000 44863198030027 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-61421101/312500000 : ℝ), (5247640023/10000000000 : ℝ), (2703638283/5000000000 : ℝ)] ![(5996249433367/50000000000000 : ℝ), (21572151542677/50000000000000 : ℝ), (44863198030027/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-61421101/312500000 : ℝ)|^1099 ≤ (5996249433367/50000000000000 : ℝ)^843
        have hw : |(-61421101/312500000 : ℝ)|=(61421101/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247640023/10000000000 : ℝ)|^1099 ≤ (21572151542677/50000000000000 : ℝ)^843
        have hw : |(5247640023/10000000000 : ℝ)|=(5247640023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703638283/5000000000 : ℝ)|^1099 ≤ (44863198030027/100000000000000 : ℝ)^843
        have hw : |(2703638283/5000000000 : ℝ)|=(2703638283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s6_5 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652673757/5000000000 : ℝ)*x 0 + (-188710817/1000000000 : ℝ)*x 1 + (5407276459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652673757/5000000000 : ℝ)^1099 ≤ (43763864625153/100000000000000 : ℝ)^843 := by
    have hnat : (2652673757 : ℕ)^1099*100000000000000^843 ≤ 43763864625153^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652673757 5000000000 43763864625153 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (188710817/1000000000 : ℝ)^1099 ≤ (5686469239323/50000000000000 : ℝ)^843 := by
    have hnat : (188710817 : ℕ)^1099*50000000000000^843 ≤ 5686469239323^843*1000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188710817 1000000000 5686469239323 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407276459/10000000000 : ℝ)^1099 ≤ (1794527874907/4000000000000 : ℝ)^843 := by
    have hnat : (5407276459 : ℕ)^1099*4000000000000^843 ≤ 1794527874907^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407276459 10000000000 1794527874907 4000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652673757/5000000000 : ℝ), (-188710817/1000000000 : ℝ), (5407276459/10000000000 : ℝ)] ![(43763864625153/100000000000000 : ℝ), (5686469239323/50000000000000 : ℝ), (1794527874907/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652673757/5000000000 : ℝ)|^1099 ≤ (43763864625153/100000000000000 : ℝ)^843
        have hw : |(2652673757/5000000000 : ℝ)|=(2652673757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-188710817/1000000000 : ℝ)|^1099 ≤ (5686469239323/50000000000000 : ℝ)^843
        have hw : |(-188710817/1000000000 : ℝ)|=(188710817/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407276459/10000000000 : ℝ)|^1099 ≤ (1794527874907/4000000000000 : ℝ)^843
        have hw : |(5407276459/10000000000 : ℝ)|=(5407276459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s6_6 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305346781/10000000000 : ℝ)*x 0 + (2703638449/5000000000 : ℝ)*x 1 + (-188710857/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305346781/10000000000 : ℝ)^1099 ≤ (10940964185609/25000000000000 : ℝ)^843 := by
    have hnat : (5305346781 : ℕ)^1099*25000000000000^843 ≤ 10940964185609^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305346781 10000000000 10940964185609 25000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2703638449/5000000000 : ℝ)^1099 ≤ (5607900202633/12500000000000 : ℝ)^843 := by
    have hnat : (2703638449 : ℕ)^1099*12500000000000^843 ≤ 5607900202633^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703638449 5000000000 5607900202633 12500000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (188710857/1000000000 : ℝ)^1099 ≤ (1421617702671/12500000000000 : ℝ)^843 := by
    have hnat : (188710857 : ℕ)^1099*12500000000000^843 ≤ 1421617702671^843*1000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188710857 1000000000 1421617702671 12500000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305346781/10000000000 : ℝ), (2703638449/5000000000 : ℝ), (-188710857/1000000000 : ℝ)] ![(10940964185609/25000000000000 : ℝ), (5607900202633/12500000000000 : ℝ), (1421617702671/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305346781/10000000000 : ℝ)|^1099 ≤ (10940964185609/25000000000000 : ℝ)^843
        have hw : |(5305346781/10000000000 : ℝ)|=(5305346781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2703638449/5000000000 : ℝ)|^1099 ≤ (5607900202633/12500000000000 : ℝ)^843
        have hw : |(2703638449/5000000000 : ℝ)|=(2703638449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-188710857/1000000000 : ℝ)|^1099 ≤ (1421617702671/12500000000000 : ℝ)^843
        have hw : |(-188710857/1000000000 : ℝ)|=(188710857/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s6_7 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (134457813/312500000 : ℝ)*x 0 + (223945741/500000000 : ℝ)*x 1 + (4132681533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134457813/312500000 : ℝ)^1099 ≤ (16652519614999/50000000000000 : ℝ)^843 := by
    have hnat : (134457813 : ℕ)^1099*50000000000000^843 ≤ 16652519614999^843*312500000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134457813 312500000 16652519614999 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (223945741/500000000 : ℝ)^1099 ≤ (7018945698141/20000000000000 : ℝ)^843 := by
    have hnat : (223945741 : ℕ)^1099*20000000000000^843 ≤ 7018945698141^843*500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223945741 500000000 7018945698141 20000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4132681533/10000000000 : ℝ)^1099 ≤ (3950029032919/12500000000000 : ℝ)^843 := by
    have hnat : (4132681533 : ℕ)^1099*12500000000000^843 ≤ 3950029032919^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4132681533 10000000000 3950029032919 12500000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134457813/312500000 : ℝ), (223945741/500000000 : ℝ), (4132681533/10000000000 : ℝ)] ![(16652519614999/50000000000000 : ℝ), (7018945698141/20000000000000 : ℝ), (3950029032919/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134457813/312500000 : ℝ)|^1099 ≤ (16652519614999/50000000000000 : ℝ)^843
        have hw : |(134457813/312500000 : ℝ)|=(134457813/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(223945741/500000000 : ℝ)|^1099 ≤ (7018945698141/20000000000000 : ℝ)^843
        have hw : |(223945741/500000000 : ℝ)|=(223945741/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4132681533/10000000000 : ℝ)|^1099 ≤ (3950029032919/12500000000000 : ℝ)^843
        have hw : |(4132681533/10000000000 : ℝ)|=(4132681533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1436_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158444201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11351/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5677/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14761/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3691/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11351/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3691/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11351/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3691/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11351/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3691/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11351/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3691/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11351/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3691/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11351/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11351/100000 : ℝ) ^ (4395/1024 : ℝ) ≤ (8794554434762561/100000000000000000000 : ℝ) := by
    have hpowers : (11351/100000 : ℝ)^4395 ≤ (8794554434762561/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11351 : ℕ)^4395*100000000000000000000^1024 ≤ 8794554434762561^1024*100000^4395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11351 100000 8794554434762561 100000000000000000000 4395 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11351/100000 : ℝ)) (X := (8794554434762561/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3691/25000 : ℝ) ^ (4395/1024 : ℝ) ≤ (1358939804523441/5000000000000000000 : ℝ) := by
    have hpowers : (3691/25000 : ℝ)^4395 ≤ (1358939804523441/5000000000000000000 : ℝ)^1024 := by
      have hnat : (3691 : ℕ)^4395*5000000000000000000^1024 ≤ 1358939804523441^1024*25000^4395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3691 25000 1358939804523441 5000000000000000000 4395 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3691/25000 : ℝ)) (X := (1358939804523441/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008794554434762561/50000000000000000000 : ℝ) ≤ (5000204892294207/5000000000000000 : ℝ) ^ (4395/1024 : ℝ) := by
    have hpowers : (50008794554434762561/50000000000000000000 : ℝ)^1024 ≤ (5000204892294207/5000000000000000 : ℝ)^4395 := by
      have hnat : (50008794554434762561 : ℕ)^1024*5000000000000000^4395 ≤ 5000204892294207^4395*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008794554434762561 50000000000000000000 5000204892294207 5000000000000000 1024 4395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000204892294207/5000000000000000 : ℝ)) (X := (50008794554434762561/50000000000000000000 : ℝ)) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035973350525231381/100000000000000000000 : ℝ) ≤ (400033521392537/400000000000000 : ℝ) ^ (4395/1024 : ℝ) := by
    have hpowers : (100035973350525231381/100000000000000000000 : ℝ)^1024 ≤ (400033521392537/400000000000000 : ℝ)^4395 := by
      have hnat : (100035973350525231381 : ℕ)^1024*400000000000000^4395 ≤ 400033521392537^4395*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035973350525231381 100000000000000000000 400033521392537 400000000000000 1024 4395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400033521392537/400000000000000 : ℝ)) (X := (100035973350525231381/100000000000000000000 : ℝ)) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501358939804523441/2500000000000000000 : ℝ) ≤ (2500316571259609/2500000000000000 : ℝ) ^ (4395/1024 : ℝ) := by
    have hpowers : (2501358939804523441/2500000000000000000 : ℝ)^1024 ≤ (2500316571259609/2500000000000000 : ℝ)^4395 := by
      have hnat : (2501358939804523441 : ℕ)^1024*2500000000000000^4395 ≤ 2500316571259609^4395*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501358939804523441 2500000000000000000 2500316571259609 2500000000000000 1024 4395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500316571259609/2500000000000000 : ℝ)) (X := (2501358939804523441/2500000000000000000 : ℝ)) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8794554434762561/100000000000000000000 : ℝ) ≤ ((1706083822909602863/1706500000000000000 : ℝ)+2*(428250225011/341300000000000 : ℝ)*(11351/100000 : ℝ))^(4395/1024 : ℝ) := by
    rw [show (1706083822909602863/1706500000000000000 : ℝ)+2*(428250225011/341300000000000 : ℝ)*(11351/100000 : ℝ)=(5000204892294207/5000000000000000 : ℝ) by norm_num, show 1+2*(8794554434762561/100000000000000000000 : ℝ)=(50008794554434762561/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1358939804523441/5000000000000000000 : ℝ)+(8794554434762561/100000000000000000000 : ℝ) ≤ ((1706083822909602863/1706500000000000000 : ℝ)+(428250225011/341300000000000 : ℝ)*((3691/25000 : ℝ)+(11351/100000 : ℝ)))^(4395/1024 : ℝ) := by
    rw [show (1706083822909602863/1706500000000000000 : ℝ)+(428250225011/341300000000000 : ℝ)*((3691/25000 : ℝ)+(11351/100000 : ℝ))=(400033521392537/400000000000000 : ℝ) by norm_num, show 1+(1358939804523441/5000000000000000000 : ℝ)+(8794554434762561/100000000000000000000 : ℝ)=(100035973350525231381/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1358939804523441/5000000000000000000 : ℝ) ≤ ((1706083822909602863/1706500000000000000 : ℝ)+2*(428250225011/341300000000000 : ℝ)*(3691/25000 : ℝ))^(4395/1024 : ℝ) := by
    rw [show (1706083822909602863/1706500000000000000 : ℝ)+2*(428250225011/341300000000000 : ℝ)*(3691/25000 : ℝ)=(2500316571259609/2500000000000000 : ℝ) by norm_num, show 1+2*(1358939804523441/5000000000000000000 : ℝ)=(2501358939804523441/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1706083822909602863/1706500000000000000 : ℝ)*(X 1 0+X 2 0)+(428250225011/341300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4395/1024 : ℝ)) (lo := (11351/100000 : ℝ)) (hi := (3691/25000 : ℝ)) (c := (1706083822909602863/1706500000000000000 : ℝ)) (alpha := (428250225011/341300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1706083822909602863/1706500000000000000 : ℝ)*(X 0 1+X 2 1)+(428250225011/341300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4395/1024 : ℝ)) (lo := (11351/100000 : ℝ)) (hi := (3691/25000 : ℝ)) (c := (1706083822909602863/1706500000000000000 : ℝ)) (alpha := (428250225011/341300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1706083822909602863/1706500000000000000 : ℝ)*(X 0 2+X 1 2)+(428250225011/341300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4395/1024 : ℝ)) (lo := (11351/100000 : ℝ)) (hi := (3691/25000 : ℝ)) (c := (1706083822909602863/1706500000000000000 : ℝ)) (alpha := (428250225011/341300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1965464227/10000000000 : ℝ)*X 0 0+(1351964971/2500000000 : ℝ)*X 0 1+(5247059521/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673589757/5000000000 : ℝ)*X 1 0+(-1023662731/5000000000 : ℝ)*X 1 1+(5247059521/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673589757/5000000000 : ℝ)*X 2 0+(5247059521/10000000000 : ℝ)*X 2 1+(-1023662731/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((860525181/2000000000 : ℝ)*X 0 0+(413141609/1000000000 : ℝ)*X 0 1+(1120043357/2500000000 : ℝ)*X 0 2+(860525181/2000000000 : ℝ)*X 1 0+(413141609/1000000000 : ℝ)*X 1 1+(1120043357/2500000000 : ℝ)*X 1 2+(860525181/2000000000 : ℝ)*X 2 0+(413141609/1000000000 : ℝ)*X 2 1+(1120043357/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-61421101/312500000 : ℝ)*X 0 0+(5247640023/10000000000 : ℝ)*X 0 1+(2703638283/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652673757/5000000000 : ℝ)*X 1 0+(-188710817/1000000000 : ℝ)*X 1 1+(5407276459/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305346781/10000000000 : ℝ)*X 2 0+(2703638449/5000000000 : ℝ)*X 2 1+(-188710857/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((134457813/312500000 : ℝ)*X 0 0+(223945741/500000000 : ℝ)*X 0 1+(4132681533/10000000000 : ℝ)*X 0 2+(134457813/312500000 : ℝ)*X 1 0+(223945741/500000000 : ℝ)*X 1 1+(4132681533/10000000000 : ℝ)*X 1 2+(134457813/312500000 : ℝ)*X 2 0+(223945741/500000000 : ℝ)*X 2 1+(4132681533/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (156860140344513284689227/17065000000000000000000000000 : ℝ) := by norm_num
    linear_combination (208460659/12500000000000 : ℝ)*(base19) + (1553498767/100000000000000 : ℝ)*(base23) + (2442303/4000000000000 : ℝ)*(lower2) + (114522159/50000000000000 : ℝ)*(upper3) + (146075601/100000000000000 : ℝ)*(upper5) + (2271580023199721/50000000000000 : ℝ)*(major0) + (2271580023199721/50000000000000 : ℝ)*(major1) + (2271580023199721/50000000000000 : ℝ)*(major2) + (1243785628159061/20000000000000 : ℝ)*(sp0) + (3109480825088293/50000000000000 : ℝ)*(sp1) + (1554740441090773/25000000000000 : ℝ)*(sp2) + (716834726796841/25000000000000 : ℝ)*(sp3) + (17588533277/50000000000000 : ℝ)*(sp4) + (17561352271/100000000000000 : ℝ)*(sp7) + (716839117134909/25000000000000 : ℝ)*(f.failure) + (6218963317861859/100000000000000 : ℝ)*(f.sum) + (121368744573317/17065000000000000000000000000 : ℝ)*base65 + (81115647220906223/85325000000000000000000000000000 : ℝ)*base67 + (3161507341743777/85325000000000000000000000000000 : ℝ)*base70 + (202353765584943777/85325000000000000000000000000000 : ℝ)*base72 + (47394113980871/8532500000000000000000000000 : ℝ)*base73 + (404380314341231223/85325000000000000000000000000000 : ℝ)*base75 + (168090004897756223/85325000000000000000000000000000 : ℝ)*base77 + (440174331889343777/85325000000000000000000000000000 : ℝ)*base80 + (60111866679347/17065000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (15712709/2500000000000000000000 : ℝ)*base89 + (15712709/2500000000000000000000 : ℝ)*base91 + (15712709/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (212622885084155543819427/17065000000000000000000000000 : ℝ) := by norm_num
    linear_combination (453302057/25000000000000 : ℝ)*(base19) + (1134048673/100000000000000 : ℝ)*(base23) + (421026689/100000000000000 : ℝ)*(lower1) + (34814723/25000000000000 : ℝ)*(upper3) + (76243997/50000000000000 : ℝ)*(lower4) + (113361251/100000000000000 : ℝ)*(upper5) + (4576200681024313/100000000000000 : ℝ)*(major0) + (4576200681024313/100000000000000 : ℝ)*(major1) + (4576200681024313/100000000000000 : ℝ)*(major2) + (12822862917/100000000000000 : ℝ)*(sp1) + (6264191310691687/100000000000000 : ℝ)*(sp4) + (6264176674620543/100000000000000 : ℝ)*(sp5) + (3132095088321507/50000000000000 : ℝ)*(sp6) + (2888209636037303/100000000000000 : ℝ)*(sp7) + (2888209636037303/100000000000000 : ℝ)*(f.failure) + (6264191310691687/100000000000000 : ℝ)*(f.sum) + (5588824975717/17065000000000000000000000000 : ℝ)*base66 + (35033877449973119/170650000000000000000000000000000 : ℝ)*base67 + (45099995347973119/170650000000000000000000000000000 : ℝ)*base69 + (1173029900657576881/170650000000000000000000000000000 : ℝ)*base72 + (6987319336797/17065000000000000000000000000 : ℝ)*base74 + (923897318040826881/170650000000000000000000000000000 : ℝ)*base76 + (465214281291323119/170650000000000000000000000000000 : ℝ)*base77 + (695467879771176881/170650000000000000000000000000000 : ℝ)*base80 + (41988207459823/4266250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (19970097/10000000000000000000000 : ℝ)*base90 + (19970097/10000000000000000000000 : ℝ)*base92 + (19970097/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1436_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158444201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11351/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5677/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1436_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1436_s7_0 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-122841669/625000000 : ℝ)*x 0 + (675979797/1250000000 : ℝ)*x 1 + (1311769847/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (122841669/625000000 : ℝ)^1099 ≤ (2398486206181/20000000000000 : ℝ)^843 := by
    have hnat : (122841669 : ℕ)^1099*20000000000000^843 ≤ 2398486206181^843*625000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122841669 625000000 2398486206181 20000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675979797/1250000000 : ℝ)^1099 ≤ (44869274873917/100000000000000 : ℝ)^843 := by
    have hnat : (675979797 : ℕ)^1099*100000000000000^843 ≤ 44869274873917^843*1250000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675979797 1250000000 44869274873917 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311769847/2500000000 : ℝ)^1099 ≤ (8627658815693/20000000000000 : ℝ)^843 := by
    have hnat : (1311769847 : ℕ)^1099*20000000000000^843 ≤ 8627658815693^843*2500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311769847 2500000000 8627658815693 20000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-122841669/625000000 : ℝ), (675979797/1250000000 : ℝ), (1311769847/2500000000 : ℝ)] ![(2398486206181/20000000000000 : ℝ), (44869274873917/100000000000000 : ℝ), (8627658815693/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-122841669/625000000 : ℝ)|^1099 ≤ (2398486206181/20000000000000 : ℝ)^843
        have hw : |(-122841669/625000000 : ℝ)|=(122841669/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675979797/1250000000 : ℝ)|^1099 ≤ (44869274873917/100000000000000 : ℝ)^843
        have hw : |(675979797/1250000000 : ℝ)|=(675979797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311769847/2500000000 : ℝ)|^1099 ≤ (8627658815693/20000000000000 : ℝ)^843
        have hw : |(1311769847/2500000000 : ℝ)|=(1311769847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s7_1 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1336793551/2500000000 : ℝ)*x 0 + (-2047306201/10000000000 : ℝ)*x 1 + (1049415867/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336793551/2500000000 : ℝ)^1099 ≤ (44214208303433/100000000000000 : ℝ)^843 := by
    have hnat : (1336793551 : ℕ)^1099*100000000000000^843 ≤ 44214208303433^843*2500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336793551 2500000000 44214208303433 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2047306201/10000000000 : ℝ)^1099 ≤ (2529499635079/20000000000000 : ℝ)^843 := by
    have hnat : (2047306201 : ℕ)^1099*20000000000000^843 ≤ 2529499635079^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2047306201 10000000000 2529499635079 20000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049415867/2000000000 : ℝ)^1099 ≤ (43138293510409/100000000000000 : ℝ)^843 := by
    have hnat : (1049415867 : ℕ)^1099*100000000000000^843 ≤ 43138293510409^843*2000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049415867 2000000000 43138293510409 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336793551/2500000000 : ℝ), (-2047306201/10000000000 : ℝ), (1049415867/2000000000 : ℝ)] ![(44214208303433/100000000000000 : ℝ), (2529499635079/20000000000000 : ℝ), (43138293510409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336793551/2500000000 : ℝ)|^1099 ≤ (44214208303433/100000000000000 : ℝ)^843
        have hw : |(1336793551/2500000000 : ℝ)|=(1336793551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2047306201/10000000000 : ℝ)|^1099 ≤ (2529499635079/20000000000000 : ℝ)^843
        have hw : |(-2047306201/10000000000 : ℝ)|=(2047306201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049415867/2000000000 : ℝ)|^1099 ≤ (43138293510409/100000000000000 : ℝ)^843
        have hw : |(1049415867/2000000000 : ℝ)|=(1049415867/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s7_2 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (213886969/400000000 : ℝ)*x 0 + (1049415869/2000000000 : ℝ)*x 1 + (-1023653079/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213886969/400000000 : ℝ)^1099 ≤ (44214208529807/100000000000000 : ℝ)^843 := by
    have hnat : (213886969 : ℕ)^1099*100000000000000^843 ≤ 44214208529807^843*400000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213886969 400000000 44214208529807 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1049415869/2000000000 : ℝ)^1099 ≤ (43138293617589/100000000000000 : ℝ)^843 := by
    have hnat : (1049415869 : ℕ)^1099*100000000000000^843 ≤ 43138293617589^843*2000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049415869 2000000000 43138293617589 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1023653079/5000000000 : ℝ)^1099 ≤ (12647497829089/100000000000000 : ℝ)^843 := by
    have hnat : (1023653079 : ℕ)^1099*100000000000000^843 ≤ 12647497829089^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023653079 5000000000 12647497829089 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213886969/400000000 : ℝ), (1049415869/2000000000 : ℝ), (-1023653079/5000000000 : ℝ)] ![(44214208529807/100000000000000 : ℝ), (43138293617589/100000000000000 : ℝ), (12647497829089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213886969/400000000 : ℝ)|^1099 ≤ (44214208529807/100000000000000 : ℝ)^843
        have hw : |(213886969/400000000 : ℝ)|=(213886969/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1049415869/2000000000 : ℝ)|^1099 ≤ (43138293617589/100000000000000 : ℝ)^843
        have hw : |(1049415869/2000000000 : ℝ)|=(1049415869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1023653079/5000000000 : ℝ)|^1099 ≤ (12647497829089/100000000000000 : ℝ)^843
        have hw : |(-1023653079/5000000000 : ℝ)|=(1023653079/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s7_3 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4302627159/10000000000 : ℝ)*x 0 + (4131461223/10000000000 : ℝ)*x 1 + (4480128153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4302627159/10000000000 : ℝ)^1099 ≤ (33304808574971/100000000000000 : ℝ)^843 := by
    have hnat : (4302627159 : ℕ)^1099*100000000000000^843 ≤ 33304808574971^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4302627159 10000000000 33304808574971 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4131461223/10000000000 : ℝ)^1099 ≤ (1579403409333/5000000000000 : ℝ)^843 := by
    have hnat : (4131461223 : ℕ)^1099*5000000000000^843 ≤ 1579403409333^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4131461223 10000000000 1579403409333 5000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4480128153/10000000000 : ℝ)^1099 ≤ (17553561610391/50000000000000 : ℝ)^843 := by
    have hnat : (4480128153 : ℕ)^1099*50000000000000^843 ≤ 17553561610391^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480128153 10000000000 17553561610391 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4302627159/10000000000 : ℝ), (4131461223/10000000000 : ℝ), (4480128153/10000000000 : ℝ)] ![(33304808574971/100000000000000 : ℝ), (1579403409333/5000000000000 : ℝ), (17553561610391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4302627159/10000000000 : ℝ)|^1099 ≤ (33304808574971/100000000000000 : ℝ)^843
        have hw : |(4302627159/10000000000 : ℝ)|=(4302627159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4131461223/10000000000 : ℝ)|^1099 ≤ (1579403409333/5000000000000 : ℝ)^843
        have hw : |(4131461223/10000000000 : ℝ)|=(4131461223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4480128153/10000000000 : ℝ)|^1099 ≤ (17553561610391/50000000000000 : ℝ)^843
        have hw : |(4480128153/10000000000 : ℝ)|=(4480128153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s7_4 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-245684691/1250000000 : ℝ)*x 0 + (5247659581/10000000000 : ℝ)*x 1 + (5407255497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (245684691/1250000000 : ℝ)^1099 ≤ (11992517130241/100000000000000 : ℝ)^843 := by
    have hnat : (245684691 : ℕ)^1099*100000000000000^843 ≤ 11992517130241^843*1250000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245684691 1250000000 11992517130241 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247659581/10000000000 : ℝ)^1099 ≤ (43144512715737/100000000000000 : ℝ)^843 := by
    have hnat : (5247659581 : ℕ)^1099*100000000000000^843 ≤ 43144512715737^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247659581 10000000000 43144512715737 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407255497/10000000000 : ℝ)^1099 ≤ (22431485069971/50000000000000 : ℝ)^843 := by
    have hnat : (5407255497 : ℕ)^1099*50000000000000^843 ≤ 22431485069971^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407255497 10000000000 22431485069971 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-245684691/1250000000 : ℝ), (5247659581/10000000000 : ℝ), (5407255497/10000000000 : ℝ)] ![(11992517130241/100000000000000 : ℝ), (43144512715737/100000000000000 : ℝ), (22431485069971/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-245684691/1250000000 : ℝ)|^1099 ≤ (11992517130241/100000000000000 : ℝ)^843
        have hw : |(-245684691/1250000000 : ℝ)|=(245684691/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247659581/10000000000 : ℝ)|^1099 ≤ (43144512715737/100000000000000 : ℝ)^843
        have hw : |(5247659581/10000000000 : ℝ)|=(5247659581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407255497/10000000000 : ℝ)|^1099 ≤ (22431485069971/50000000000000 : ℝ)^843
        have hw : |(5407255497/10000000000 : ℝ)|=(5407255497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s7_5 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (265267627/500000000 : ℝ)*x 0 + (-1887130123/10000000000 : ℝ)*x 1 + (5407255517/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265267627/500000000 : ℝ)^1099 ≤ (43763918675003/100000000000000 : ℝ)^843 := by
    have hnat : (265267627 : ℕ)^1099*100000000000000^843 ≤ 43763918675003^843*500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265267627 500000000 43763918675003 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1887130123/10000000000 : ℝ)^1099 ≤ (5686555479703/50000000000000 : ℝ)^843 := by
    have hnat : (1887130123 : ℕ)^1099*50000000000000^843 ≤ 5686555479703^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1887130123 10000000000 5686555479703 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407255517/10000000000 : ℝ)^1099 ≤ (4486297035627/10000000000000 : ℝ)^843 := by
    have hnat : (5407255517 : ℕ)^1099*10000000000000^843 ≤ 4486297035627^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407255517 10000000000 4486297035627 10000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265267627/500000000 : ℝ), (-1887130123/10000000000 : ℝ), (5407255517/10000000000 : ℝ)] ![(43763918675003/100000000000000 : ℝ), (5686555479703/50000000000000 : ℝ), (4486297035627/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265267627/500000000 : ℝ)|^1099 ≤ (43763918675003/100000000000000 : ℝ)^843
        have hw : |(265267627/500000000 : ℝ)|=(265267627/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1887130123/10000000000 : ℝ)|^1099 ≤ (5686555479703/50000000000000 : ℝ)^843
        have hw : |(-1887130123/10000000000 : ℝ)|=(1887130123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407255517/10000000000 : ℝ)|^1099 ≤ (4486297035627/10000000000000 : ℝ)^843
        have hw : |(5407255517/10000000000 : ℝ)|=(5407255517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s7_6 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1326338139/2500000000 : ℝ)*x 0 + (216290221/400000000 : ℝ)*x 1 + (-1887130089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326338139/2500000000 : ℝ)^1099 ≤ (43763918847067/100000000000000 : ℝ)^843 := by
    have hnat : (1326338139 : ℕ)^1099*100000000000000^843 ≤ 43763918847067^843*2500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326338139 2500000000 43763918847067 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216290221/400000000 : ℝ)^1099 ≤ (112157426107/250000000000 : ℝ)^843 := by
    have hnat : (216290221 : ℕ)^1099*250000000000^843 ≤ 112157426107^843*400000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216290221 400000000 112157426107 250000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1887130089/10000000000 : ℝ)^1099 ≤ (5686555346137/50000000000000 : ℝ)^843 := by
    have hnat : (1887130089 : ℕ)^1099*50000000000000^843 ≤ 5686555346137^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1887130089 10000000000 5686555346137 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326338139/2500000000 : ℝ), (216290221/400000000 : ℝ), (-1887130089/10000000000 : ℝ)] ![(43763918847067/100000000000000 : ℝ), (112157426107/250000000000 : ℝ), (5686555346137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326338139/2500000000 : ℝ)|^1099 ≤ (43763918847067/100000000000000 : ℝ)^843
        have hw : |(1326338139/2500000000 : ℝ)|=(1326338139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216290221/400000000 : ℝ)|^1099 ≤ (112157426107/250000000000 : ℝ)^843
        have hw : |(216290221/400000000 : ℝ)|=(216290221/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1887130089/10000000000 : ℝ)|^1099 ≤ (5686555346137/50000000000000 : ℝ)^843
        have hw : |(-1887130089/10000000000 : ℝ)|=(1887130089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_s7_7 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (215132591/500000000 : ℝ)*x 0 + (89577407/200000000 : ℝ)*x 1 + (4132725277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215132591/500000000 : ℝ)^1099 ≤ (2081566089661/6250000000000 : ℝ)^843 := by
    have hnat : (215132591 : ℕ)^1099*6250000000000^843 ≤ 2081566089661^843*500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215132591 500000000 2081566089661 6250000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89577407/200000000 : ℝ)^1099 ≤ (35094274229471/100000000000000 : ℝ)^843 := by
    have hnat : (89577407 : ℕ)^1099*100000000000000^843 ≤ 35094274229471^843*200000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89577407 200000000 35094274229471 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4132725277/10000000000 : ℝ)^1099 ≤ (31600668324751/100000000000000 : ℝ)^843 := by
    have hnat : (4132725277 : ℕ)^1099*100000000000000^843 ≤ 31600668324751^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4132725277 10000000000 31600668324751 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215132591/500000000 : ℝ), (89577407/200000000 : ℝ), (4132725277/10000000000 : ℝ)] ![(2081566089661/6250000000000 : ℝ), (35094274229471/100000000000000 : ℝ), (31600668324751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215132591/500000000 : ℝ)|^1099 ≤ (2081566089661/6250000000000 : ℝ)^843
        have hw : |(215132591/500000000 : ℝ)|=(215132591/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(89577407/200000000 : ℝ)|^1099 ≤ (35094274229471/100000000000000 : ℝ)^843
        have hw : |(89577407/200000000 : ℝ)|=(89577407/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4132725277/10000000000 : ℝ)|^1099 ≤ (31600668324751/100000000000000 : ℝ)^843
        have hw : |(4132725277/10000000000 : ℝ)|=(4132725277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1436_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158444201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5677/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2271/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (369/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14761/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5677/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14761/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5677/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14761/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5677/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14761/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5677/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14761/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5677/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14761/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5677/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5677/50000 : ℝ) ^ (4395/1024 : ℝ) ≤ (4402267427428429/50000000000000000000 : ℝ) := by
    have hpowers : (5677/50000 : ℝ)^4395 ≤ (4402267427428429/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5677 : ℕ)^4395*50000000000000000000^1024 ≤ 4402267427428429^1024*50000^4395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5677 50000 4402267427428429 50000000000000000000 4395 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5677/50000 : ℝ)) (X := (4402267427428429/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14761/100000 : ℝ) ^ (4395/1024 : ℝ) ≤ (27155100851125037/100000000000000000000 : ℝ) := by
    have hpowers : (14761/100000 : ℝ)^4395 ≤ (27155100851125037/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14761 : ℕ)^4395*100000000000000000000^1024 ≤ 27155100851125037^1024*100000^4395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14761 100000 27155100851125037 100000000000000000000 4395 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14761/100000 : ℝ)) (X := (27155100851125037/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004402267427428429/25000000000000000000 : ℝ) ≤ (400016409983893/400000000000000 : ℝ) ^ (4395/1024 : ℝ) := by
    have hpowers : (25004402267427428429/25000000000000000000 : ℝ)^1024 ≤ (400016409983893/400000000000000 : ℝ)^4395 := by
      have hnat : (25004402267427428429 : ℕ)^1024*400000000000000^4395 ≤ 400016409983893^4395*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004402267427428429 25000000000000000000 400016409983893 400000000000000 1024 4395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400016409983893/400000000000000 : ℝ)) (X := (25004402267427428429/25000000000000000000 : ℝ)) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20007191927141196379/20000000000000000000 : ℝ) ≤ (5000418857678591/5000000000000000 : ℝ) ^ (4395/1024 : ℝ) := by
    have hpowers : (20007191927141196379/20000000000000000000 : ℝ)^1024 ≤ (5000418857678591/5000000000000000 : ℝ)^4395 := by
      have hnat : (20007191927141196379 : ℕ)^1024*5000000000000000^4395 ≤ 5000418857678591^4395*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20007191927141196379 20000000000000000000 5000418857678591 5000000000000000 1024 4395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000418857678591/5000000000000000 : ℝ)) (X := (20007191927141196379/20000000000000000000 : ℝ)) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027155100851125037/50000000000000000000 : ℝ) ≤ (10001265181117039/10000000000000000 : ℝ) ^ (4395/1024 : ℝ) := by
    have hpowers : (50027155100851125037/50000000000000000000 : ℝ)^1024 ≤ (10001265181117039/10000000000000000 : ℝ)^4395 := by
      have hnat : (50027155100851125037 : ℕ)^1024*10000000000000000^4395 ≤ 10001265181117039^4395*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027155100851125037 50000000000000000000 10001265181117039 10000000000000000 1024 4395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001265181117039/10000000000000000 : ℝ)) (X := (50027155100851125037/50000000000000000000 : ℝ)) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4402267427428429/50000000000000000000 : ℝ) ≤ ((34061690827903253519/34070000000000000000 : ℝ)+2*(427465759857/340700000000000 : ℝ)*(5677/50000 : ℝ))^(4395/1024 : ℝ) := by
    rw [show (34061690827903253519/34070000000000000000 : ℝ)+2*(427465759857/340700000000000 : ℝ)*(5677/50000 : ℝ)=(400016409983893/400000000000000 : ℝ) by norm_num, show 1+2*(4402267427428429/50000000000000000000 : ℝ)=(25004402267427428429/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27155100851125037/100000000000000000000 : ℝ)+(4402267427428429/50000000000000000000 : ℝ) ≤ ((34061690827903253519/34070000000000000000 : ℝ)+(427465759857/340700000000000 : ℝ)*((14761/100000 : ℝ)+(5677/50000 : ℝ)))^(4395/1024 : ℝ) := by
    rw [show (34061690827903253519/34070000000000000000 : ℝ)+(427465759857/340700000000000 : ℝ)*((14761/100000 : ℝ)+(5677/50000 : ℝ))=(5000418857678591/5000000000000000 : ℝ) by norm_num, show 1+(27155100851125037/100000000000000000000 : ℝ)+(4402267427428429/50000000000000000000 : ℝ)=(20007191927141196379/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27155100851125037/100000000000000000000 : ℝ) ≤ ((34061690827903253519/34070000000000000000 : ℝ)+2*(427465759857/340700000000000 : ℝ)*(14761/100000 : ℝ))^(4395/1024 : ℝ) := by
    rw [show (34061690827903253519/34070000000000000000 : ℝ)+2*(427465759857/340700000000000 : ℝ)*(14761/100000 : ℝ)=(10001265181117039/10000000000000000 : ℝ) by norm_num, show 1+2*(27155100851125037/100000000000000000000 : ℝ)=(50027155100851125037/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34061690827903253519/34070000000000000000 : ℝ)*(X 1 0+X 2 0)+(427465759857/340700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4395/1024 : ℝ)) (lo := (5677/50000 : ℝ)) (hi := (14761/100000 : ℝ)) (c := (34061690827903253519/34070000000000000000 : ℝ)) (alpha := (427465759857/340700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34061690827903253519/34070000000000000000 : ℝ)*(X 0 1+X 2 1)+(427465759857/340700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4395/1024 : ℝ)) (lo := (5677/50000 : ℝ)) (hi := (14761/100000 : ℝ)) (c := (34061690827903253519/34070000000000000000 : ℝ)) (alpha := (427465759857/340700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34061690827903253519/34070000000000000000 : ℝ)*(X 0 2+X 1 2)+(427465759857/340700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4395/1024 : ℝ)) (lo := (5677/50000 : ℝ)) (hi := (14761/100000 : ℝ)) (c := (34061690827903253519/34070000000000000000 : ℝ)) (alpha := (427465759857/340700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-122841669/625000000 : ℝ)*X 0 0+(675979797/1250000000 : ℝ)*X 0 1+(1311769847/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336793551/2500000000 : ℝ)*X 1 0+(-2047306201/10000000000 : ℝ)*X 1 1+(1049415867/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213886969/400000000 : ℝ)*X 2 0+(1049415869/2000000000 : ℝ)*X 2 1+(-1023653079/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4302627159/10000000000 : ℝ)*X 0 0+(4131461223/10000000000 : ℝ)*X 0 1+(4480128153/10000000000 : ℝ)*X 0 2+(4302627159/10000000000 : ℝ)*X 1 0+(4131461223/10000000000 : ℝ)*X 1 1+(4480128153/10000000000 : ℝ)*X 1 2+(4302627159/10000000000 : ℝ)*X 2 0+(4131461223/10000000000 : ℝ)*X 2 1+(4480128153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-245684691/1250000000 : ℝ)*X 0 0+(5247659581/10000000000 : ℝ)*X 0 1+(5407255497/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265267627/500000000 : ℝ)*X 1 0+(-1887130123/10000000000 : ℝ)*X 1 1+(5407255517/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326338139/2500000000 : ℝ)*X 2 0+(216290221/400000000 : ℝ)*X 2 1+(-1887130089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((215132591/500000000 : ℝ)*X 0 0+(89577407/200000000 : ℝ)*X 0 1+(4132725277/10000000000 : ℝ)*X 0 2+(215132591/500000000 : ℝ)*X 1 0+(89577407/200000000 : ℝ)*X 1 1+(4132725277/10000000000 : ℝ)*X 1 2+(215132591/500000000 : ℝ)*X 2 0+(89577407/200000000 : ℝ)*X 2 1+(4132725277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2858628834063677600839207587/1703500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (20562871/1562500000000 : ℝ)*(base19) + (831852159/100000000000000 : ℝ)*(base23) + (423387/1562500000000 : ℝ)*(upper2) + (300490509/100000000000000 : ℝ)*(upper3) + (149527433/50000000000000 : ℝ)*(upper4) + (4544306644651791/100000000000000 : ℝ)*(major0) + (4544306644651791/100000000000000 : ℝ)*(major1) + (4544306644651791/100000000000000 : ℝ)*(major2) + (3110257436014061/50000000000000 : ℝ)*(sp0) + (3110265894102939/50000000000000 : ℝ)*(sp1) + (6220532272377463/100000000000000 : ℝ)*(sp2) + (1434035045397509/50000000000000 : ℝ)*(sp3) + (36464403/200000000000 : ℝ)*(sp4) + (1254792819/12500000000000 : ℝ)*(sp7) + (286808012913757/10000000000000 : ℝ)*(f.failure) + (3110266552114811/50000000000000 : ℝ)*(f.sum) + (133751544634397/17035000000000000000000000000 : ℝ)*base65 + (35611726138362897471/3407000000000000000000000000000000 : ℝ)*base68 + (19565512178918897471/3407000000000000000000000000000000 : ℝ)*base70 + (43933860410241102529/3407000000000000000000000000000000 : ℝ)*base71 + (39601285033873/17035000000000000000000000000 : ℝ)*base74 + (50876306532576897471/3407000000000000000000000000000000 : ℝ)*base76 + (18920620155600102529/3407000000000000000000000000000000 : ℝ)*base77 + (31695108315103897471/3407000000000000000000000000000000 : ℝ)*base80 + (60597890483247/17035000000000000000000000000 : ℝ)*base81 + (226843/1000000000000000000000 : ℝ)*base90 + (226843/1000000000000000000000 : ℝ)*base92 + (226843/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (892396125717280462895165433/170350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (218448823/25000000000000 : ℝ)*(base19) + (988123179/100000000000000 : ℝ)*(base23) + (287021759/100000000000000 : ℝ)*(lower1) + (126821703/100000000000000 : ℝ)*(upper3) + (37057513/100000000000000 : ℝ)*(lower4) + (29426403/25000000000000 : ℝ)*(upper5) + (915475958558931/20000000000000 : ℝ)*(major0) + (915475958558931/20000000000000 : ℝ)*(major1) + (915475958558931/20000000000000 : ℝ)*(major2) + (1622625903/50000000000000 : ℝ)*(sp2) + (3132902796924627/50000000000000 : ℝ)*(sp4) + (3132902360026981/50000000000000 : ℝ)*(sp5) + (6265801360474269/100000000000000 : ℝ)*(sp6) + (1444476908559959/50000000000000 : ℝ)*(sp7) + (1444476908559959/50000000000000 : ℝ)*(f.failure) + (3132902796924627/50000000000000 : ℝ)*(f.sum) + (19304376676869/3407000000000000000000000000 : ℝ)*base66 + (22942042768862271811/681400000000000000000000000000000 : ℝ)*base68 + (786020553427728189/681400000000000000000000000000000 : ℝ)*base69 + (76546322729745328189/681400000000000000000000000000000 : ℝ)*base71 + (21568489416551/3407000000000000000000000000 : ℝ)*base74 + (1820822451785328189/681400000000000000000000000000000 : ℝ)*base75 + (5097772468817728189/681400000000000000000000000000000 : ℝ)*base77 + (338444277848328189/681400000000000000000000000000000 : ℝ)*base79 + (33482714527/13308593750000000000000000 : ℝ)*base82 + (14347759/5000000000000000000000 : ℝ)*base89 + (14347759/5000000000000000000000 : ℝ)*base91 + (14347759/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1436_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158444201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14761/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5677/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2271/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (369/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1436_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1436_box_0 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-902656579/5000000000 : ℝ)*x 0 + (168311107/312500000 : ℝ)*x 1 + (1077191061/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (902656579/5000000000 : ℝ)^1099 ≤ (10734563777237/100000000000000 : ℝ)^843 := by
    have hnat : (902656579 : ℕ)^1099*100000000000000^843 ≤ 10734563777237^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902656579 5000000000 10734563777237 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168311107/312500000 : ℝ)^1099 ≤ (4463271874687/10000000000000 : ℝ)^843 := by
    have hnat : (168311107 : ℕ)^1099*10000000000000^843 ≤ 4463271874687^843*312500000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168311107 312500000 4463271874687 10000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077191061/2000000000 : ℝ)^1099 ≤ (8926543492253/20000000000000 : ℝ)^843 := by
    have hnat : (1077191061 : ℕ)^1099*20000000000000^843 ≤ 8926543492253^843*2000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077191061 2000000000 8926543492253 20000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-902656579/5000000000 : ℝ), (168311107/312500000 : ℝ), (1077191061/2000000000 : ℝ)] ![(10734563777237/100000000000000 : ℝ), (4463271874687/10000000000000 : ℝ), (8926543492253/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-902656579/5000000000 : ℝ)|^1099 ≤ (10734563777237/100000000000000 : ℝ)^843
        have hw : |(-902656579/5000000000 : ℝ)|=(902656579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168311107/312500000 : ℝ)|^1099 ≤ (4463271874687/10000000000000 : ℝ)^843
        have hw : |(168311107/312500000 : ℝ)|=(168311107/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077191061/2000000000 : ℝ)|^1099 ≤ (8926543492253/20000000000000 : ℝ)^843
        have hw : |(1077191061/2000000000 : ℝ)|=(1077191061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_box_1 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5286113549/10000000000 : ℝ)*x 0 + (-1942509887/10000000000 : ℝ)*x 1 + (1346488841/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286113549/10000000000 : ℝ)^1099 ≤ (43557135611251/100000000000000 : ℝ)^843 := by
    have hnat : (5286113549 : ℕ)^1099*100000000000000^843 ≤ 43557135611251^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286113549 10000000000 43557135611251 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1942509887/10000000000 : ℝ)^1099 ≤ (11810146285413/100000000000000 : ℝ)^843 := by
    have hnat : (1942509887 : ℕ)^1099*100000000000000^843 ≤ 11810146285413^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1942509887 10000000000 11810146285413 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346488841/2500000000 : ℝ)^1099 ≤ (22316359049333/50000000000000 : ℝ)^843 := by
    have hnat : (1346488841 : ℕ)^1099*50000000000000^843 ≤ 22316359049333^843*2500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346488841 2500000000 22316359049333 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286113549/10000000000 : ℝ), (-1942509887/10000000000 : ℝ), (1346488841/2500000000 : ℝ)] ![(43557135611251/100000000000000 : ℝ), (11810146285413/100000000000000 : ℝ), (22316359049333/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286113549/10000000000 : ℝ)|^1099 ≤ (43557135611251/100000000000000 : ℝ)^843
        have hw : |(5286113549/10000000000 : ℝ)|=(5286113549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1942509887/10000000000 : ℝ)|^1099 ≤ (11810146285413/100000000000000 : ℝ)^843
        have hw : |(-1942509887/10000000000 : ℝ)|=(1942509887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346488841/2500000000 : ℝ)|^1099 ≤ (22316359049333/50000000000000 : ℝ)^843
        have hw : |(1346488841/2500000000 : ℝ)|=(1346488841/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_box_2 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5286113797/10000000000 : ℝ)*x 0 + (673244389/1250000000 : ℝ)*x 1 + (-485627473/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5286113797/10000000000 : ℝ)^1099 ≤ (8711427655063/20000000000000 : ℝ)^843 := by
    have hnat : (5286113797 : ℕ)^1099*20000000000000^843 ≤ 8711427655063^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5286113797 10000000000 8711427655063 20000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (673244389/1250000000 : ℝ)^1099 ≤ (2789544711013/6250000000000 : ℝ)^843 := by
    have hnat : (673244389 : ℕ)^1099*6250000000000^843 ≤ 2789544711013^843*1250000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673244389 1250000000 2789544711013 6250000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (485627473/2500000000 : ℝ)^1099 ≤ (2952536581261/25000000000000 : ℝ)^843 := by
    have hnat : (485627473 : ℕ)^1099*25000000000000^843 ≤ 2952536581261^843*2500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      485627473 2500000000 2952536581261 25000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5286113797/10000000000 : ℝ), (673244389/1250000000 : ℝ), (-485627473/2500000000 : ℝ)] ![(8711427655063/20000000000000 : ℝ), (2789544711013/6250000000000 : ℝ), (2952536581261/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5286113797/10000000000 : ℝ)|^1099 ≤ (8711427655063/20000000000000 : ℝ)^843
        have hw : |(5286113797/10000000000 : ℝ)|=(5286113797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(673244389/1250000000 : ℝ)|^1099 ≤ (2789544711013/6250000000000 : ℝ)^843
        have hw : |(673244389/1250000000 : ℝ)|=(673244389/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-485627473/2500000000 : ℝ)|^1099 ≤ (2952536581261/25000000000000 : ℝ)^843
        have hw : |(-485627473/2500000000 : ℝ)|=(485627473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_box_3 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4448783129/10000000000 : ℝ)*x 0 + (846648903/2000000000 : ℝ)*x 1 + (4233244879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4448783129/10000000000 : ℝ)^1099 ≤ (1087101486889/3125000000000 : ℝ)^843 := by
    have hnat : (4448783129 : ℕ)^1099*3125000000000^843 ≤ 1087101486889^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4448783129 10000000000 1087101486889 3125000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846648903/2000000000 : ℝ)^1099 ≤ (3260637436861/10000000000000 : ℝ)^843 := by
    have hnat : (846648903 : ℕ)^1099*10000000000000^843 ≤ 3260637436861^843*2000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846648903 2000000000 3260637436861 10000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4233244879/10000000000 : ℝ)^1099 ≤ (16303189011861/50000000000000 : ℝ)^843 := by
    have hnat : (4233244879 : ℕ)^1099*50000000000000^843 ≤ 16303189011861^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233244879 10000000000 16303189011861 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4448783129/10000000000 : ℝ), (846648903/2000000000 : ℝ), (4233244879/10000000000 : ℝ)] ![(1087101486889/3125000000000 : ℝ), (3260637436861/10000000000000 : ℝ), (16303189011861/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4448783129/10000000000 : ℝ)|^1099 ≤ (1087101486889/3125000000000 : ℝ)^843
        have hw : |(4448783129/10000000000 : ℝ)|=(4448783129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(846648903/2000000000 : ℝ)|^1099 ≤ (3260637436861/10000000000000 : ℝ)^843
        have hw : |(846648903/2000000000 : ℝ)|=(846648903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4233244879/10000000000 : ℝ)|^1099 ≤ (16303189011861/50000000000000 : ℝ)^843
        have hw : |(4233244879/10000000000 : ℝ)|=(4233244879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_box_4 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2128353517/10000000000 : ℝ)*x 0 + (2633314359/5000000000 : ℝ)*x 1 + (210665157/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128353517/10000000000 : ℝ)^1099 ≤ (6652055835927/50000000000000 : ℝ)^843 := by
    have hnat : (2128353517 : ℕ)^1099*50000000000000^843 ≤ 6652055835927^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128353517 10000000000 6652055835927 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633314359/5000000000 : ℝ)^1099 ≤ (21673971523977/50000000000000 : ℝ)^843 := by
    have hnat : (2633314359 : ℕ)^1099*50000000000000^843 ≤ 21673971523977^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633314359 5000000000 21673971523977 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210665157/400000000 : ℝ)^1099 ≤ (5418493158637/12500000000000 : ℝ)^843 := by
    have hnat : (210665157 : ℕ)^1099*12500000000000^843 ≤ 5418493158637^843*400000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210665157 400000000 5418493158637 12500000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2128353517/10000000000 : ℝ), (2633314359/5000000000 : ℝ), (210665157/400000000 : ℝ)] ![(6652055835927/50000000000000 : ℝ), (21673971523977/50000000000000 : ℝ), (5418493158637/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2128353517/10000000000 : ℝ)|^1099 ≤ (6652055835927/50000000000000 : ℝ)^843
        have hw : |(-2128353517/10000000000 : ℝ)|=(2128353517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633314359/5000000000 : ℝ)|^1099 ≤ (21673971523977/50000000000000 : ℝ)^843
        have hw : |(2633314359/5000000000 : ℝ)|=(2633314359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210665157/400000000 : ℝ)|^1099 ≤ (5418493158637/12500000000000 : ℝ)^843
        have hw : |(210665157/400000000 : ℝ)|=(210665157/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_box_5 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5369600207/10000000000 : ℝ)*x 0 + (-199100137/1000000000 : ℝ)*x 1 + (164582157/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369600207/10000000000 : ℝ)^1099 ≤ (22228054110431/50000000000000 : ℝ)^843 := by
    have hnat : (5369600207 : ℕ)^1099*50000000000000^843 ≤ 22228054110431^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369600207 10000000000 22228054110431 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (199100137/1000000000 : ℝ)^1099 ≤ (6097972713263/50000000000000 : ℝ)^843 := by
    have hnat : (199100137 : ℕ)^1099*50000000000000^843 ≤ 6097972713263^843*1000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199100137 1000000000 6097972713263 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164582157/312500000 : ℝ)^1099 ≤ (43347946331381/100000000000000 : ℝ)^843 := by
    have hnat : (164582157 : ℕ)^1099*100000000000000^843 ≤ 43347946331381^843*312500000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164582157 312500000 43347946331381 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369600207/10000000000 : ℝ), (-199100137/1000000000 : ℝ), (164582157/312500000 : ℝ)] ![(22228054110431/50000000000000 : ℝ), (6097972713263/50000000000000 : ℝ), (43347946331381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369600207/10000000000 : ℝ)|^1099 ≤ (22228054110431/50000000000000 : ℝ)^843
        have hw : |(5369600207/10000000000 : ℝ)|=(5369600207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-199100137/1000000000 : ℝ)|^1099 ≤ (6097972713263/50000000000000 : ℝ)^843
        have hw : |(-199100137/1000000000 : ℝ)|=(199100137/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164582157/312500000 : ℝ)|^1099 ≤ (43347946331381/100000000000000 : ℝ)^843
        have hw : |(164582157/312500000 : ℝ)|=(164582157/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_box_6 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5369600291/10000000000 : ℝ)*x 0 + (5266628881/10000000000 : ℝ)*x 1 + (-1991001449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369600291/10000000000 : ℝ)^1099 ≤ (4445610912751/10000000000000 : ℝ)^843 := by
    have hnat : (5369600291 : ℕ)^1099*10000000000000^843 ≤ 4445610912751^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369600291 10000000000 4445610912751 10000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266628881/10000000000 : ℝ)^1099 ≤ (43347944796969/100000000000000 : ℝ)^843 := by
    have hnat : (5266628881 : ℕ)^1099*100000000000000^843 ≤ 43347944796969^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266628881 10000000000 43347944796969 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1991001449/10000000000 : ℝ)^1099 ≤ (6097973028699/50000000000000 : ℝ)^843 := by
    have hnat : (1991001449 : ℕ)^1099*50000000000000^843 ≤ 6097973028699^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1991001449 10000000000 6097973028699 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369600291/10000000000 : ℝ), (5266628881/10000000000 : ℝ), (-1991001449/10000000000 : ℝ)] ![(4445610912751/10000000000000 : ℝ), (43347944796969/100000000000000 : ℝ), (6097973028699/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369600291/10000000000 : ℝ)|^1099 ≤ (4445610912751/10000000000000 : ℝ)^843
        have hw : |(5369600291/10000000000 : ℝ)|=(5369600291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266628881/10000000000 : ℝ)|^1099 ≤ (43347944796969/100000000000000 : ℝ)^843
        have hw : |(5266628881/10000000000 : ℝ)|=(5266628881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1991001449/10000000000 : ℝ)|^1099 ≤ (6097973028699/50000000000000 : ℝ)^843
        have hw : |(-1991001449/10000000000 : ℝ)|=(1991001449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_box_7 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2077707153/5000000000 : ℝ)*x 0 + (4379878411/10000000000 : ℝ)*x 1 + (1094969607/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2077707153/5000000000 : ℝ)^1099 ≤ (31827032230993/100000000000000 : ℝ)^843 := by
    have hnat : (2077707153 : ℕ)^1099*100000000000000^843 ≤ 31827032230993^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2077707153 5000000000 31827032230993 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4379878411/10000000000 : ℝ)^1099 ≤ (34086483789861/100000000000000 : ℝ)^843 := by
    have hnat : (4379878411 : ℕ)^1099*100000000000000^843 ≤ 34086483789861^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4379878411 10000000000 34086483789861 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1094969607/2500000000 : ℝ)^1099 ≤ (34086483962341/100000000000000 : ℝ)^843 := by
    have hnat : (1094969607 : ℕ)^1099*100000000000000^843 ≤ 34086483962341^843*2500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094969607 2500000000 34086483962341 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2077707153/5000000000 : ℝ), (4379878411/10000000000 : ℝ), (1094969607/2500000000 : ℝ)] ![(31827032230993/100000000000000 : ℝ), (34086483789861/100000000000000 : ℝ), (34086483962341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2077707153/5000000000 : ℝ)|^1099 ≤ (31827032230993/100000000000000 : ℝ)^843
        have hw : |(2077707153/5000000000 : ℝ)|=(2077707153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4379878411/10000000000 : ℝ)|^1099 ≤ (34086483789861/100000000000000 : ℝ)^843
        have hw : |(4379878411/10000000000 : ℝ)|=(4379878411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1094969607/2500000000 : ℝ)|^1099 ≤ (34086483962341/100000000000000 : ℝ)^843
        have hw : |(1094969607/2500000000 : ℝ)|=(1094969607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_box_8 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2060296271/10000000000 : ℝ)*x 0 + (81000943/156250000 : ℝ)*x 1 + (2699962413/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2060296271/10000000000 : ℝ)^1099 ≤ (2550443219739/20000000000000 : ℝ)^843 := by
    have hnat : (2060296271 : ℕ)^1099*20000000000000^843 ≤ 2550443219739^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060296271 10000000000 2550443219739 20000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (81000943/156250000 : ℝ)^1099 ≤ (21232044308171/50000000000000 : ℝ)^843 := by
    have hnat : (81000943 : ℕ)^1099*50000000000000^843 ≤ 21232044308171^843*156250000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81000943 156250000 21232044308171 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699962413/5000000000 : ℝ)^1099 ≤ (22391847634669/50000000000000 : ℝ)^843 := by
    have hnat : (2699962413 : ℕ)^1099*50000000000000^843 ≤ 22391847634669^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699962413 5000000000 22391847634669 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2060296271/10000000000 : ℝ), (81000943/156250000 : ℝ), (2699962413/5000000000 : ℝ)] ![(2550443219739/20000000000000 : ℝ), (21232044308171/50000000000000 : ℝ), (22391847634669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2060296271/10000000000 : ℝ)|^1099 ≤ (2550443219739/20000000000000 : ℝ)^843
        have hw : |(-2060296271/10000000000 : ℝ)|=(2060296271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(81000943/156250000 : ℝ)|^1099 ≤ (21232044308171/50000000000000 : ℝ)^843
        have hw : |(81000943/156250000 : ℝ)|=(81000943/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699962413/5000000000 : ℝ)|^1099 ≤ (22391847634669/50000000000000 : ℝ)^843
        have hw : |(2699962413/5000000000 : ℝ)|=(2699962413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_box_9 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5276335789/10000000000 : ℝ)*x 0 + (-968353623/5000000000 : ℝ)*x 1 + (539992479/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276335789/10000000000 : ℝ)^1099 ≤ (43452130540723/100000000000000 : ℝ)^843 := by
    have hnat : (5276335789 : ℕ)^1099*100000000000000^843 ≤ 43452130540723^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276335789 10000000000 43452130540723 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (968353623/5000000000 : ℝ)^1099 ≤ (5882087285799/50000000000000 : ℝ)^843 := by
    have hnat : (968353623 : ℕ)^1099*50000000000000^843 ≤ 5882087285799^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      968353623 5000000000 5882087285799 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539992479/1000000000 : ℝ)^1099 ≤ (44783694880109/100000000000000 : ℝ)^843 := by
    have hnat : (539992479 : ℕ)^1099*100000000000000^843 ≤ 44783694880109^843*1000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539992479 1000000000 44783694880109 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276335789/10000000000 : ℝ), (-968353623/5000000000 : ℝ), (539992479/1000000000 : ℝ)] ![(43452130540723/100000000000000 : ℝ), (5882087285799/50000000000000 : ℝ), (44783694880109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276335789/10000000000 : ℝ)|^1099 ≤ (43452130540723/100000000000000 : ℝ)^843
        have hw : |(5276335789/10000000000 : ℝ)|=(5276335789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-968353623/5000000000 : ℝ)|^1099 ≤ (5882087285799/50000000000000 : ℝ)^843
        have hw : |(-968353623/5000000000 : ℝ)|=(968353623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539992479/1000000000 : ℝ)|^1099 ≤ (44783694880109/100000000000000 : ℝ)^843
        have hw : |(539992479/1000000000 : ℝ)|=(539992479/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_box_10 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5276335741/10000000000 : ℝ)*x 0 + (5399924823/10000000000 : ℝ)*x 1 + (-30261051/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276335741/10000000000 : ℝ)^1099 ≤ (10863032506347/25000000000000 : ℝ)^843 := by
    have hnat : (5276335741 : ℕ)^1099*25000000000000^843 ≤ 10863032506347^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276335741 10000000000 10863032506347 25000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399924823/10000000000 : ℝ)^1099 ≤ (22391847618451/50000000000000 : ℝ)^843 := by
    have hnat : (5399924823 : ℕ)^1099*50000000000000^843 ≤ 22391847618451^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399924823 10000000000 22391847618451 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (30261051/156250000 : ℝ)^1099 ≤ (11764174714139/100000000000000 : ℝ)^843 := by
    have hnat : (30261051 : ℕ)^1099*100000000000000^843 ≤ 11764174714139^843*156250000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30261051 156250000 11764174714139 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276335741/10000000000 : ℝ), (5399924823/10000000000 : ℝ), (-30261051/156250000 : ℝ)] ![(10863032506347/25000000000000 : ℝ), (22391847618451/50000000000000 : ℝ), (11764174714139/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276335741/10000000000 : ℝ)|^1099 ≤ (10863032506347/25000000000000 : ℝ)^843
        have hw : |(5276335741/10000000000 : ℝ)|=(5276335741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399924823/10000000000 : ℝ)|^1099 ≤ (22391847618451/50000000000000 : ℝ)^843
        have hw : |(5399924823/10000000000 : ℝ)|=(5399924823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-30261051/156250000 : ℝ)|^1099 ≤ (11764174714139/100000000000000 : ℝ)^843
        have hw : |(-30261051/156250000 : ℝ)|=(30261051/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_box_11 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (112064267/250000000 : ℝ)*x 0 + (4216063909/10000000000 : ℝ)*x 1 + (4216063837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (112064267/250000000 : ℝ)^1099 ≤ (35132077799517/100000000000000 : ℝ)^843 := by
    have hnat : (112064267 : ℕ)^1099*100000000000000^843 ≤ 35132077799517^843*250000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112064267 250000000 35132077799517 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4216063909/10000000000 : ℝ)^1099 ≤ (6486792291163/20000000000000 : ℝ)^843 := by
    have hnat : (4216063909 : ℕ)^1099*20000000000000^843 ≤ 6486792291163^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216063909 10000000000 6486792291163 20000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4216063837/10000000000 : ℝ)^1099 ≤ (32433960733719/100000000000000 : ℝ)^843 := by
    have hnat : (4216063837 : ℕ)^1099*100000000000000^843 ≤ 32433960733719^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4216063837 10000000000 32433960733719 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(112064267/250000000 : ℝ), (4216063909/10000000000 : ℝ), (4216063837/10000000000 : ℝ)] ![(35132077799517/100000000000000 : ℝ), (6486792291163/20000000000000 : ℝ), (32433960733719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(112064267/250000000 : ℝ)|^1099 ≤ (35132077799517/100000000000000 : ℝ)^843
        have hw : |(112064267/250000000 : ℝ)|=(112064267/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4216063909/10000000000 : ℝ)|^1099 ≤ (6486792291163/20000000000000 : ℝ)^843
        have hw : |(4216063909/10000000000 : ℝ)|=(4216063909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4216063837/10000000000 : ℝ)|^1099 ≤ (32433960733719/100000000000000 : ℝ)^843
        have hw : |(4216063837/10000000000 : ℝ)|=(4216063837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_box_12 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-936769141/5000000000 : ℝ)*x 0 + (5466513819/10000000000 : ℝ)*x 1 + (5255499891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (936769141/5000000000 : ℝ)^1099 ≤ (11266439108573/100000000000000 : ℝ)^843 := by
    have hnat : (936769141 : ℕ)^1099*100000000000000^843 ≤ 11266439108573^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936769141 5000000000 11266439108573 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5466513819/10000000000 : ℝ)^1099 ≤ (11376248378747/25000000000000 : ℝ)^843 := by
    have hnat : (5466513819 : ℕ)^1099*25000000000000^843 ≤ 11376248378747^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466513819 10000000000 11376248378747 25000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255499891/10000000000 : ℝ)^1099 ≤ (43228567365607/100000000000000 : ℝ)^843 := by
    have hnat : (5255499891 : ℕ)^1099*100000000000000^843 ≤ 43228567365607^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255499891 10000000000 43228567365607 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-936769141/5000000000 : ℝ), (5466513819/10000000000 : ℝ), (5255499891/10000000000 : ℝ)] ![(11266439108573/100000000000000 : ℝ), (11376248378747/25000000000000 : ℝ), (43228567365607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-936769141/5000000000 : ℝ)|^1099 ≤ (11266439108573/100000000000000 : ℝ)^843
        have hw : |(-936769141/5000000000 : ℝ)|=(936769141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5466513819/10000000000 : ℝ)|^1099 ≤ (11376248378747/25000000000000 : ℝ)^843
        have hw : |(5466513819/10000000000 : ℝ)|=(5466513819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255499891/10000000000 : ℝ)|^1099 ≤ (43228567365607/100000000000000 : ℝ)^843
        have hw : |(5255499891/10000000000 : ℝ)|=(5255499891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_box_13 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (336086523/625000000 : ℝ)*x 0 + (-997712371/5000000000 : ℝ)*x 1 + (5255500539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336086523/625000000 : ℝ)^1099 ≤ (44540144529953/100000000000000 : ℝ)^843 := by
    have hnat : (336086523 : ℕ)^1099*100000000000000^843 ≤ 44540144529953^843*625000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336086523 625000000 44540144529953 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (997712371/5000000000 : ℝ)^1099 ≤ (611564057141/5000000000000 : ℝ)^843 := by
    have hnat : (997712371 : ℕ)^1099*5000000000000^843 ≤ 611564057141^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997712371 5000000000 611564057141 5000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255500539/10000000000 : ℝ)^1099 ≤ (43228574314281/100000000000000 : ℝ)^843 := by
    have hnat : (5255500539 : ℕ)^1099*100000000000000^843 ≤ 43228574314281^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255500539 10000000000 43228574314281 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336086523/625000000 : ℝ), (-997712371/5000000000 : ℝ), (5255500539/10000000000 : ℝ)] ![(44540144529953/100000000000000 : ℝ), (611564057141/5000000000000 : ℝ), (43228574314281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336086523/625000000 : ℝ)|^1099 ≤ (44540144529953/100000000000000 : ℝ)^843
        have hw : |(336086523/625000000 : ℝ)|=(336086523/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-997712371/5000000000 : ℝ)|^1099 ≤ (611564057141/5000000000000 : ℝ)^843
        have hw : |(-997712371/5000000000 : ℝ)|=(997712371/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255500539/10000000000 : ℝ)|^1099 ≤ (43228574314281/100000000000000 : ℝ)^843
        have hw : |(5255500539/10000000000 : ℝ)|=(5255500539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_box_14 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5377385881/10000000000 : ℝ)*x 0 + (5255498957/10000000000 : ℝ)*x 1 + (-99771241/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5377385881/10000000000 : ℝ)^1099 ≤ (44540160867603/100000000000000 : ℝ)^843 := by
    have hnat : (5377385881 : ℕ)^1099*100000000000000^843 ≤ 44540160867603^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5377385881 10000000000 44540160867603 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5255498957/10000000000 : ℝ)^1099 ≤ (43228557350081/100000000000000 : ℝ)^843 := by
    have hnat : (5255498957 : ℕ)^1099*100000000000000^843 ≤ 43228557350081^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255498957 10000000000 43228557350081 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (99771241/500000000 : ℝ)^1099 ≤ (6115640883063/50000000000000 : ℝ)^843 := by
    have hnat : (99771241 : ℕ)^1099*50000000000000^843 ≤ 6115640883063^843*500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99771241 500000000 6115640883063 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5377385881/10000000000 : ℝ), (5255498957/10000000000 : ℝ), (-99771241/500000000 : ℝ)] ![(44540160867603/100000000000000 : ℝ), (43228557350081/100000000000000 : ℝ), (6115640883063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5377385881/10000000000 : ℝ)|^1099 ≤ (44540160867603/100000000000000 : ℝ)^843
        have hw : |(5377385881/10000000000 : ℝ)|=(5377385881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5255498957/10000000000 : ℝ)|^1099 ≤ (43228557350081/100000000000000 : ℝ)^843
        have hw : |(5255498957/10000000000 : ℝ)|=(5255498957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-99771241/500000000 : ℝ)|^1099 ≤ (6115640883063/50000000000000 : ℝ)^843
        have hw : |(-99771241/500000000 : ℝ)|=(99771241/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1436_box_15 (p : ℝ) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1031900751/2500000000 : ℝ)*x 0 + (2196771909/5000000000 : ℝ)*x 1 + (4393542741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1031900751/2500000000 : ℝ)^1099 ≤ (31549616554423/100000000000000 : ℝ)^843 := by
    have hnat : (1031900751 : ℕ)^1099*100000000000000^843 ≤ 31549616554423^843*2500000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031900751 2500000000 31549616554423 100000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2196771909/5000000000 : ℝ)^1099 ≤ (17112598589787/50000000000000 : ℝ)^843 := by
    have hnat : (2196771909 : ℕ)^1099*50000000000000^843 ≤ 17112598589787^843*5000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196771909 5000000000 17112598589787 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4393542741/10000000000 : ℝ)^1099 ≤ (17112593121053/50000000000000 : ℝ)^843 := by
    have hnat : (4393542741 : ℕ)^1099*50000000000000^843 ≤ 17112593121053^843*10000000000^1099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4393542741 10000000000 17112593121053 50000000000000 1099 843 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1099/256 : ℝ)) 1099 843 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1031900751/2500000000 : ℝ), (2196771909/5000000000 : ℝ), (4393542741/10000000000 : ℝ)] ![(31549616554423/100000000000000 : ℝ), (17112598589787/50000000000000 : ℝ), (17112593121053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1031900751/2500000000 : ℝ)|^1099 ≤ (31549616554423/100000000000000 : ℝ)^843
        have hw : |(1031900751/2500000000 : ℝ)|=(1031900751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2196771909/5000000000 : ℝ)|^1099 ≤ (17112598589787/50000000000000 : ℝ)^843
        have hw : |(2196771909/5000000000 : ℝ)|=(2196771909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4393542741/10000000000 : ℝ)|^1099 ≤ (17112593121053/50000000000000 : ℝ)^843
        have hw : |(4393542741/10000000000 : ℝ)|=(4393542741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1436_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158444201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (369/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2271/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(7863/12500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(59127/100000 : ℝ) ∧ (80487/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84711/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (369/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2271/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (369/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2271/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (369/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2271/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (369/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2271/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (369/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2271/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (369/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2271/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2271/20000 : ℝ) ^ (4395/1024 : ℝ) ≤ (4403931795645497/50000000000000000000 : ℝ) := by
    have hpowers : (2271/20000 : ℝ)^4395 ≤ (4403931795645497/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2271 : ℕ)^4395*50000000000000000000^1024 ≤ 4403931795645497^1024*20000^4395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2271 20000 4403931795645497 50000000000000000000 4395 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2271/20000 : ℝ)) (X := (4403931795645497/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (369/2500 : ℝ) ^ (4395/1024 : ℝ) ≤ (6786801490049607/25000000000000000000 : ℝ) := by
    have hpowers : (369/2500 : ℝ)^4395 ≤ (6786801490049607/25000000000000000000 : ℝ)^1024 := by
      have hnat : (369 : ℕ)^4395*25000000000000000000^1024 ≤ 6786801490049607^1024*2500^4395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        369 2500 6786801490049607 25000000000000000000 4395 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (369/2500 : ℝ)) (X := (6786801490049607/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004403931795645497/25000000000000000000 : ℝ) ≤ (10000410404690191/10000000000000000 : ℝ) ^ (4395/1024 : ℝ) := by
    have hpowers : (25004403931795645497/25000000000000000000 : ℝ)^1024 ≤ (10000410404690191/10000000000000000 : ℝ)^4395 := by
      have hnat : (25004403931795645497 : ℕ)^1024*10000000000000000^4395 ≤ 10000410404690191^4395*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004403931795645497 25000000000000000000 10000410404690191 10000000000000000 1024 4395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000410404690191/10000000000000000 : ℝ)) (X := (25004403931795645497/25000000000000000000 : ℝ)) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017977534775744711/50000000000000000000 : ℝ) ≤ (10000837608998751/10000000000000000 : ℝ) ^ (4395/1024 : ℝ) := by
    have hpowers : (50017977534775744711/50000000000000000000 : ℝ)^1024 ≤ (10000837608998751/10000000000000000 : ℝ)^4395 := by
      have hnat : (50017977534775744711 : ℕ)^1024*10000000000000000^4395 ≤ 10000837608998751^4395*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017977534775744711 50000000000000000000 10000837608998751 10000000000000000 1024 4395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000837608998751/10000000000000000 : ℝ)) (X := (50017977534775744711/50000000000000000000 : ℝ)) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506786801490049607/12500000000000000000 : ℝ) ≤ (10001264813307311/10000000000000000 : ℝ) ^ (4395/1024 : ℝ) := by
    have hpowers : (12506786801490049607/12500000000000000000 : ℝ)^1024 ≤ (10001264813307311/10000000000000000 : ℝ)^4395 := by
      have hnat : (12506786801490049607 : ℕ)^1024*10000000000000000^4395 ≤ 10001264813307311^4395*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506786801490049607 12500000000000000000 10001264813307311 10000000000000000 1024 4395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001264813307311/10000000000000000 : ℝ)) (X := (12506786801490049607/12500000000000000000 : ℝ)) (by norm_num) 4395 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4403931795645497/50000000000000000000 : ℝ) ≤ ((2269446374541513517/2270000000000000000 : ℝ)+2*(5340053857/4256250000000 : ℝ)*(2271/20000 : ℝ))^(4395/1024 : ℝ) := by
    rw [show (2269446374541513517/2270000000000000000 : ℝ)+2*(5340053857/4256250000000 : ℝ)*(2271/20000 : ℝ)=(10000410404690191/10000000000000000 : ℝ) by norm_num, show 1+2*(4403931795645497/50000000000000000000 : ℝ)=(25004403931795645497/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6786801490049607/25000000000000000000 : ℝ)+(4403931795645497/50000000000000000000 : ℝ) ≤ ((2269446374541513517/2270000000000000000 : ℝ)+(5340053857/4256250000000 : ℝ)*((369/2500 : ℝ)+(2271/20000 : ℝ)))^(4395/1024 : ℝ) := by
    rw [show (2269446374541513517/2270000000000000000 : ℝ)+(5340053857/4256250000000 : ℝ)*((369/2500 : ℝ)+(2271/20000 : ℝ))=(10000837608998751/10000000000000000 : ℝ) by norm_num, show 1+(6786801490049607/25000000000000000000 : ℝ)+(4403931795645497/50000000000000000000 : ℝ)=(50017977534775744711/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6786801490049607/25000000000000000000 : ℝ) ≤ ((2269446374541513517/2270000000000000000 : ℝ)+2*(5340053857/4256250000000 : ℝ)*(369/2500 : ℝ))^(4395/1024 : ℝ) := by
    rw [show (2269446374541513517/2270000000000000000 : ℝ)+2*(5340053857/4256250000000 : ℝ)*(369/2500 : ℝ)=(10001264813307311/10000000000000000 : ℝ) by norm_num, show 1+2*(6786801490049607/25000000000000000000 : ℝ)=(12506786801490049607/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2269446374541513517/2270000000000000000 : ℝ)*(X 1 0+X 2 0)+(5340053857/4256250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4395/1024 : ℝ)) (lo := (2271/20000 : ℝ)) (hi := (369/2500 : ℝ)) (c := (2269446374541513517/2270000000000000000 : ℝ)) (alpha := (5340053857/4256250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2269446374541513517/2270000000000000000 : ℝ)*(X 0 1+X 2 1)+(5340053857/4256250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4395/1024 : ℝ)) (lo := (2271/20000 : ℝ)) (hi := (369/2500 : ℝ)) (c := (2269446374541513517/2270000000000000000 : ℝ)) (alpha := (5340053857/4256250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2269446374541513517/2270000000000000000 : ℝ)*(X 0 2+X 1 2)+(5340053857/4256250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4395/1024 : ℝ)) (lo := (2271/20000 : ℝ)) (hi := (369/2500 : ℝ)) (c := (2269446374541513517/2270000000000000000 : ℝ)) (alpha := (5340053857/4256250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-902656579/5000000000 : ℝ)*X 0 0+(168311107/312500000 : ℝ)*X 0 1+(1077191061/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5286113549/10000000000 : ℝ)*X 1 0+(-1942509887/10000000000 : ℝ)*X 1 1+(1346488841/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5286113797/10000000000 : ℝ)*X 2 0+(673244389/1250000000 : ℝ)*X 2 1+(-485627473/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4448783129/10000000000 : ℝ)*X 0 0+(846648903/2000000000 : ℝ)*X 0 1+(4233244879/10000000000 : ℝ)*X 0 2+(4448783129/10000000000 : ℝ)*X 1 0+(846648903/2000000000 : ℝ)*X 1 1+(4233244879/10000000000 : ℝ)*X 1 2+(4448783129/10000000000 : ℝ)*X 2 0+(846648903/2000000000 : ℝ)*X 2 1+(4233244879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2128353517/10000000000 : ℝ)*X 0 0+(2633314359/5000000000 : ℝ)*X 0 1+(210665157/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5369600207/10000000000 : ℝ)*X 1 0+(-199100137/1000000000 : ℝ)*X 1 1+(164582157/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5369600291/10000000000 : ℝ)*X 2 0+(5266628881/10000000000 : ℝ)*X 2 1+(-1991001449/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2077707153/5000000000 : ℝ)*X 0 0+(4379878411/10000000000 : ℝ)*X 0 1+(1094969607/2500000000 : ℝ)*X 0 2+(2077707153/5000000000 : ℝ)*X 1 0+(4379878411/10000000000 : ℝ)*X 1 1+(1094969607/2500000000 : ℝ)*X 1 2+(2077707153/5000000000 : ℝ)*X 2 0+(4379878411/10000000000 : ℝ)*X 2 1+(1094969607/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2060296271/10000000000 : ℝ)*X 0 0+(81000943/156250000 : ℝ)*X 0 1+(2699962413/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5276335789/10000000000 : ℝ)*X 1 0+(-968353623/5000000000 : ℝ)*X 1 1+(539992479/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5276335741/10000000000 : ℝ)*X 2 0+(5399924823/10000000000 : ℝ)*X 2 1+(-30261051/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((112064267/250000000 : ℝ)*X 0 0+(4216063909/10000000000 : ℝ)*X 0 1+(4216063837/10000000000 : ℝ)*X 0 2+(112064267/250000000 : ℝ)*X 1 0+(4216063909/10000000000 : ℝ)*X 1 1+(4216063837/10000000000 : ℝ)*X 1 2+(112064267/250000000 : ℝ)*X 2 0+(4216063909/10000000000 : ℝ)*X 2 1+(4216063837/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-936769141/5000000000 : ℝ)*X 0 0+(5466513819/10000000000 : ℝ)*X 0 1+(5255499891/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((336086523/625000000 : ℝ)*X 1 0+(-997712371/5000000000 : ℝ)*X 1 1+(5255500539/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5377385881/10000000000 : ℝ)*X 2 0+(5255498957/10000000000 : ℝ)*X 2 1+(-99771241/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1031900751/2500000000 : ℝ)*X 0 0+(2196771909/5000000000 : ℝ)*X 0 1+(4393542741/10000000000 : ℝ)*X 0 2+(1031900751/2500000000 : ℝ)*X 1 0+(2196771909/5000000000 : ℝ)*X 1 1+(4393542741/10000000000 : ℝ)*X 1 2+(1031900751/2500000000 : ℝ)*X 2 0+(2196771909/5000000000 : ℝ)*X 2 1+(4393542741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1436_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-7863/12500 : ℝ) ≤ (-71392940594763029604823659407863/113500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (42683899/100000000000000 : ℝ)*(upper1) + (36134389/100000000000000 : ℝ)*(lower4) + (5359351/10000000000000 : ℝ)*(upper5) + (3024474005954287/100000000000000 : ℝ)*(major0) + (3024474005954287/100000000000000 : ℝ)*(major1) + (3024474005954287/100000000000000 : ℝ)*(major2) + (1345877493/100000000000000 : ℝ)*(sp2) + (809664477/100000000000000 : ℝ)*(sp3) + (832211218270247/20000000000000 : ℝ)*(sp4) + (4160980718600763/100000000000000 : ℝ)*(sp5) + (4161056260923223/100000000000000 : ℝ)*(sp6) + (954428342596103/50000000000000 : ℝ)*(sp7) + (1515449481/100000000000000 : ℝ)*(sp12) + (38444099977/50000000000000 : ℝ)*(sp13) + (1908857494856683/100000000000000 : ℝ)*(f.failure) + (1040264401700179/25000000000000 : ℝ)*(f.sum) + (28936351061/13300781250000000000000000 : ℝ)*base66 + (2922806088428192137/681000000000000000000000000000000 : ℝ)*base67 + (3226551560261192137/681000000000000000000000000000000 : ℝ)*base69 + (805860675723807863/681000000000000000000000000000000 : ℝ)*base72 + (51563917429/3405000000000000000000000000 : ℝ)*base73 + (1727138850270807863/681000000000000000000000000000000 : ℝ)*base76 + (2791283352204807863/681000000000000000000000000000000 : ℝ)*base78 + (1139939811381807863/681000000000000000000000000000000 : ℝ)*base80 + (2289219736837/425625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (47445283/10000000000000000000000 : ℝ)*base89 + (47445283/10000000000000000000000 : ℝ)*base91 + (47445283/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (59127/100000 : ℝ) ≤ (33556147476669072871248052958717/56750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11152801/12500000000000 : ℝ)*(lower1) + (2806631/10000000000000 : ℝ)*(lower2) + (828723/6250000000000 : ℝ)*(lower3) + (1260981/6250000000000 : ℝ)*(upper4) + (1548158172982711/50000000000000 : ℝ)*(major0) + (1548158172982711/50000000000000 : ℝ)*(major1) + (1548158172982711/50000000000000 : ℝ)*(major2) + (421872291198113/10000000000000 : ℝ)*(sp0) + (1054671587967899/25000000000000 : ℝ)*(sp1) + (1054657172720117/25000000000000 : ℝ)*(sp2) + (977099676037377/50000000000000 : ℝ)*(sp3) + (251389257/50000000000000 : ℝ)*(sp7) + (18280054767/50000000000000 : ℝ)*(sp9) + (94221100663/100000000000000 : ℝ)*(sp10) + (488549963713317/25000000000000 : ℝ)*(f.failure) + (421872291198113/10000000000000 : ℝ)*(f.sum) + (7501717399207/1702500000000000000000000000 : ℝ)*base65 + (4653462279862613761/340500000000000000000000000000000 : ℝ)*base67 + (3151281588340613761/340500000000000000000000000000000 : ℝ)*base69 + (5137881961024613761/340500000000000000000000000000000 : ℝ)*base71 + (977959036631/851250000000000000000000000 : ℝ)*base73 + (4345076578903613761/340500000000000000000000000000000 : ℝ)*base75 + (3302536992990113761/340500000000000000000000000000000 : ℝ)*base77 + (3559823628090113761/340500000000000000000000000000000 : ℝ)*base79 + (2387998285943/1702500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (44875283/2500000000000000000000 : ℝ)*base90 + (44875283/2500000000000000000000 : ℝ)*base92 + (44875283/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80487/100000 : ℝ) ≤ (913556281592028882796756473/1135000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19781843/100000000000000 : ℝ)*(upper1) + (16871521/100000000000000 : ℝ)*(upper2) + (1441499/20000000000000 : ℝ)*(lower5) + (3403822795409613/100000000000000 : ℝ)*(major0) + (3403822795409613/100000000000000 : ℝ)*(major1) + (3403822795409613/100000000000000 : ℝ)*(major2) + (9011776709/100000000000000 : ℝ)*(sp1) + (579917189/4000000000000 : ℝ)*(sp2) + (2668265949/50000000000000 : ℝ)*(sp3) + (177879141/25000000000000 : ℝ)*(sp4) + (926507295046759/20000000000000 : ℝ)*(sp8) + (4632528174973649/100000000000000 : ℝ)*(sp9) + (4632522688820633/100000000000000 : ℝ)*(sp10) + (2148273220794169/100000000000000 : ℝ)*(sp11) + (1074139278663033/50000000000000 : ℝ)*(f.failure) + (2316268593375179/50000000000000 : ℝ)*(f.sum) + (8662978013263/1135000000000000000000000000 : ℝ)*base66 + (1033246141534561079/227000000000000000000000000000000 : ℝ)*base68 + (1177971871548561079/227000000000000000000000000000000 : ℝ)*base70 + (760371390378438921/227000000000000000000000000000000 : ℝ)*base71 + (5262826777319/567500000000000000000000000 : ℝ)*base74 + (3478486525019438921/227000000000000000000000000000000 : ℝ)*base75 + (133306175373561079/227000000000000000000000000000000 : ℝ)*base78 + (1094493783156438921/227000000000000000000000000000000 : ℝ)*base79 + (2908776866553/1135000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (38078367/5000000000000000000000 : ℝ)*base90 + (38078367/5000000000000000000000 : ℝ)*base92 + (38078367/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-84711/100000 : ℝ) ≤ (-12018014053521940796626737150101/14187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (189072277/50000000000000 : ℝ)*(lower2) + (134463583/50000000000000 : ℝ)*(upper3) + (23823349/12500000000000 : ℝ)*(upper5) + (430174251192949/12500000000000 : ℝ)*(major0) + (430174251192949/12500000000000 : ℝ)*(major1) + (430174251192949/12500000000000 : ℝ)*(major2) + (7626616981/50000000000000 : ℝ)*(sp4) + (43525428863/10000000000000 : ℝ)*(sp6) + (168281960919/100000000000000 : ℝ)*(sp7) + (733488263/50000000000000 : ℝ)*(sp8) + (592377039249217/12500000000000 : ℝ)*(sp12) + (74047391159441/1562500000000 : ℝ)*(sp13) + (2369298889957797/50000000000000 : ℝ)*(sp14) + (2171822859288607/100000000000000 : ℝ)*(sp15) + (86879645649981/4000000000000 : ℝ)*(f.failure) + (74047391159441/1562500000000 : ℝ)*(f.sum) + (7615941353723/1702500000000000000000000000 : ℝ)*base66 + (272292750638699899/85125000000000000000000000000000 : ℝ)*base67 + (261485122543050101/85125000000000000000000000000000 : ℝ)*base70 + (174016262720324899/85125000000000000000000000000000 : ℝ)*base71 + (240991697431/3405000000000000000000000000 : ℝ)*base74 + (38220007512300101/85125000000000000000000000000000 : ℝ)*base76 + (144023438951175101/85125000000000000000000000000000 : ℝ)*base78 + (99371753275800101/85125000000000000000000000000000 : ℝ)*base80 + (9172811120941/3405000000000000000000000000 : ℝ)*base82 + (2789819/400000000000000000000 : ℝ)*base90 + (2789819/400000000000000000000 : ℝ)*base92 + (2789819/400000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1436_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158444201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (369/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2271/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7863/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(59127/100000 : ℝ) else (80487/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84711/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1436_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1436_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158444201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11351/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7863/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(59127/100000 : ℝ) else (80487/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84711/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1436_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1436_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1436_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4395/1024 : ℝ) ≤ p) (hpb : p ≤ (1099/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (158444201/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3691/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11351/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7863/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(59127/100000 : ℝ) else (80487/100000 : ℝ) ≤ X j i ∧ X j i ≤ (84711/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1436_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
