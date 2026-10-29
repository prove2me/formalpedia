-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1768_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:30:49.931981+00:00
-- url     : https://prove2.me/submissions/03123005-c6d7-4d2d-bb68-09d81b24f313

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
theorem support_rectangle_w1768_s0_0 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1095916867/10000000000 : ℝ)*x 0 + (2789551211/5000000000 : ℝ)*x 1 + (2501172091/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1095916867/10000000000 : ℝ)^6063 ≤ (174817981077/2500000000000 : ℝ)^5039 := by
    have hnat : (1095916867 : ℕ)^6063*2500000000000^5039 ≤ 174817981077^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095916867 10000000000 174817981077 2500000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2789551211/5000000000 : ℝ)^6063 ≤ (19356305127/39062500000 : ℝ)^5039 := by
    have hnat : (2789551211 : ℕ)^6063*39062500000^5039 ≤ 19356305127^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2789551211 5000000000 19356305127 39062500000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2501172091/5000000000 : ℝ)^6063 ≤ (43455139619277/100000000000000 : ℝ)^5039 := by
    have hnat : (2501172091 : ℕ)^6063*100000000000000^5039 ≤ 43455139619277^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2501172091 5000000000 43455139619277 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1095916867/10000000000 : ℝ), (2789551211/5000000000 : ℝ), (2501172091/5000000000 : ℝ)] ![(174817981077/2500000000000 : ℝ), (19356305127/39062500000 : ℝ), (43455139619277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1095916867/10000000000 : ℝ)|^6063 ≤ (174817981077/2500000000000 : ℝ)^5039
        have hw : |(-1095916867/10000000000 : ℝ)|=(1095916867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2789551211/5000000000 : ℝ)|^6063 ≤ (19356305127/39062500000 : ℝ)^5039
        have hw : |(2789551211/5000000000 : ℝ)|=(2789551211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2501172091/5000000000 : ℝ)|^6063 ≤ (43455139619277/100000000000000 : ℝ)^5039
        have hw : |(2501172091/5000000000 : ℝ)|=(2501172091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_s0_1 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668973849/1250000000 : ℝ)*x 0 + (-56113943/400000000 : ℝ)*x 1 + (5002343621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668973849/1250000000 : ℝ)^6063 ≤ (9426622046157/20000000000000 : ℝ)^5039 := by
    have hnat : (668973849 : ℕ)^6063*20000000000000^5039 ≤ 9426622046157^5039*1250000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668973849 1250000000 9426622046157 20000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56113943/400000000 : ℝ)^6063 ≤ (4705877997091/50000000000000 : ℝ)^5039 := by
    have hnat : (56113943 : ℕ)^6063*50000000000000^5039 ≤ 4705877997091^5039*400000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56113943 400000000 4705877997091 50000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5002343621/10000000000 : ℝ)^6063 ≤ (43455133755551/100000000000000 : ℝ)^5039 := by
    have hnat : (5002343621 : ℕ)^6063*100000000000000^5039 ≤ 43455133755551^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5002343621 10000000000 43455133755551 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668973849/1250000000 : ℝ), (-56113943/400000000 : ℝ), (5002343621/10000000000 : ℝ)] ![(9426622046157/20000000000000 : ℝ), (4705877997091/50000000000000 : ℝ), (43455133755551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668973849/1250000000 : ℝ)|^6063 ≤ (9426622046157/20000000000000 : ℝ)^5039
        have hw : |(668973849/1250000000 : ℝ)|=(668973849/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-56113943/400000000 : ℝ)|^6063 ≤ (4705877997091/50000000000000 : ℝ)^5039
        have hw : |(-56113943/400000000 : ℝ)|=(56113943/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5002343621/10000000000 : ℝ)|^6063 ≤ (43455133755551/100000000000000 : ℝ)^5039
        have hw : |(5002343621/10000000000 : ℝ)|=(5002343621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_s0_2 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351787091/10000000000 : ℝ)*x 0 + (125058653/250000000 : ℝ)*x 1 + (-701425099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351787091/10000000000 : ℝ)^6063 ≤ (47133071012443/100000000000000 : ℝ)^5039 := by
    have hnat : (5351787091 : ℕ)^6063*100000000000000^5039 ≤ 47133071012443^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351787091 10000000000 47133071012443 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125058653/250000000 : ℝ)^6063 ≤ (8691031975157/20000000000000 : ℝ)^5039 := by
    have hnat : (125058653 : ℕ)^6063*20000000000000^5039 ≤ 8691031975157^5039*250000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125058653 250000000 8691031975157 20000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (701425099/5000000000 : ℝ)^6063 ≤ (9411769095701/100000000000000 : ℝ)^5039 := by
    have hnat : (701425099 : ℕ)^6063*100000000000000^5039 ≤ 9411769095701^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      701425099 5000000000 9411769095701 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351787091/10000000000 : ℝ), (125058653/250000000 : ℝ), (-701425099/5000000000 : ℝ)] ![(47133071012443/100000000000000 : ℝ), (8691031975157/20000000000000 : ℝ), (9411769095701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351787091/10000000000 : ℝ)|^6063 ≤ (47133071012443/100000000000000 : ℝ)^5039
        have hw : |(5351787091/10000000000 : ℝ)|=(5351787091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(125058653/250000000 : ℝ)|^6063 ≤ (8691031975157/20000000000000 : ℝ)^5039
        have hw : |(125058653/250000000 : ℝ)|=(125058653/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-701425099/5000000000 : ℝ)|^6063 ≤ (9411769095701/100000000000000 : ℝ)^5039
        have hw : |(-701425099/5000000000 : ℝ)|=(701425099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_s0_3 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3951669777/10000000000 : ℝ)*x 0 + (749943629/2500000000 : ℝ)*x 1 + (314653979/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3951669777/10000000000 : ℝ)^6063 ≤ (32722046321289/100000000000000 : ℝ)^5039 := by
    have hnat : (3951669777 : ℕ)^6063*100000000000000^5039 ≤ 32722046321289^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3951669777 10000000000 32722046321289 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (749943629/2500000000 : ℝ)^6063 ≤ (23486873757453/100000000000000 : ℝ)^5039 := by
    have hnat : (749943629 : ℕ)^6063*100000000000000^5039 ≤ 23486873757453^5039*2500000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      749943629 2500000000 23486873757453 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (314653979/625000000 : ℝ)^6063 ≤ (43791079904539/100000000000000 : ℝ)^5039 := by
    have hnat : (314653979 : ℕ)^6063*100000000000000^5039 ≤ 43791079904539^5039*625000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314653979 625000000 43791079904539 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3951669777/10000000000 : ℝ), (749943629/2500000000 : ℝ), (314653979/625000000 : ℝ)] ![(32722046321289/100000000000000 : ℝ), (23486873757453/100000000000000 : ℝ), (43791079904539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3951669777/10000000000 : ℝ)|^6063 ≤ (32722046321289/100000000000000 : ℝ)^5039
        have hw : |(3951669777/10000000000 : ℝ)|=(3951669777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(749943629/2500000000 : ℝ)|^6063 ≤ (23486873757453/100000000000000 : ℝ)^5039
        have hw : |(749943629/2500000000 : ℝ)|=(749943629/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(314653979/625000000 : ℝ)|^6063 ≤ (43791079904539/100000000000000 : ℝ)^5039
        have hw : |(314653979/625000000 : ℝ)|=(314653979/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_s0_4 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-8775661/80000000 : ℝ)*x 0 + (200665167/400000000 : ℝ)*x 1 + (111287499/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8775661/80000000 : ℝ)^6063 ≤ (280028411351/4000000000000 : ℝ)^5039 := by
    have hnat : (8775661 : ℕ)^6063*4000000000000^5039 ≤ 280028411351^5039*80000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8775661 80000000 280028411351 4000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200665167/400000000 : ℝ)^6063 ≤ (21802246786073/50000000000000 : ℝ)^5039 := by
    have hnat : (200665167 : ℕ)^6063*50000000000000^5039 ≤ 21802246786073^5039*400000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200665167 400000000 21802246786073 50000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (111287499/200000000 : ℝ)^6063 ≤ (49394796133823/100000000000000 : ℝ)^5039 := by
    have hnat : (111287499 : ℕ)^6063*100000000000000^5039 ≤ 49394796133823^5039*200000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111287499 200000000 49394796133823 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-8775661/80000000 : ℝ), (200665167/400000000 : ℝ), (111287499/200000000 : ℝ)] ![(280028411351/4000000000000 : ℝ), (21802246786073/50000000000000 : ℝ), (49394796133823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-8775661/80000000 : ℝ)|^6063 ≤ (280028411351/4000000000000 : ℝ)^5039
        have hw : |(-8775661/80000000 : ℝ)|=(8775661/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(200665167/400000000 : ℝ)|^6063 ≤ (21802246786073/50000000000000 : ℝ)^5039
        have hw : |(200665167/400000000 : ℝ)|=(200665167/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(111287499/200000000 : ℝ)|^6063 ≤ (49394796133823/100000000000000 : ℝ)^5039
        have hw : |(111287499/200000000 : ℝ)|=(111287499/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_s0_5 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2599626359/5000000000 : ℝ)*x 0 + (-168163899/2000000000 : ℝ)*x 1 + (1391093737/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2599626359/5000000000 : ℝ)^6063 ≤ (9104285756499/20000000000000 : ℝ)^5039 := by
    have hnat : (2599626359 : ℕ)^6063*20000000000000^5039 ≤ 9104285756499^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2599626359 5000000000 9104285756499 20000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168163899/2000000000 : ℝ)^6063 ≤ (2541887544139/50000000000000 : ℝ)^5039 := by
    have hnat : (168163899 : ℕ)^6063*50000000000000^5039 ≤ 2541887544139^5039*2000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168163899 2000000000 2541887544139 50000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1391093737/2500000000 : ℝ)^6063 ≤ (49394796112461/100000000000000 : ℝ)^5039 := by
    have hnat : (1391093737 : ℕ)^6063*100000000000000^5039 ≤ 49394796112461^5039*2500000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1391093737 2500000000 49394796112461 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2599626359/5000000000 : ℝ), (-168163899/2000000000 : ℝ), (1391093737/2500000000 : ℝ)] ![(9104285756499/20000000000000 : ℝ), (2541887544139/50000000000000 : ℝ), (49394796112461/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2599626359/5000000000 : ℝ)|^6063 ≤ (9104285756499/20000000000000 : ℝ)^5039
        have hw : |(2599626359/5000000000 : ℝ)|=(2599626359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-168163899/2000000000 : ℝ)|^6063 ≤ (2541887544139/50000000000000 : ℝ)^5039
        have hw : |(-168163899/2000000000 : ℝ)|=(168163899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1391093737/2500000000 : ℝ)|^6063 ≤ (49394796112461/100000000000000 : ℝ)^5039
        have hw : |(1391093737/2500000000 : ℝ)|=(1391093737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_s0_6 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5199253043/10000000000 : ℝ)*x 0 + (5564374843/10000000000 : ℝ)*x 1 + (-840819179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5199253043/10000000000 : ℝ)^6063 ≤ (45521432206241/100000000000000 : ℝ)^5039 := by
    have hnat : (5199253043 : ℕ)^6063*100000000000000^5039 ≤ 45521432206241^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5199253043 10000000000 45521432206241 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5564374843/10000000000 : ℝ)^6063 ≤ (24697397495483/50000000000000 : ℝ)^5039 := by
    have hnat : (5564374843 : ℕ)^6063*50000000000000^5039 ≤ 24697397495483^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5564374843 10000000000 24697397495483 50000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (840819179/10000000000 : ℝ)^6063 ≤ (5083772789411/100000000000000 : ℝ)^5039 := by
    have hnat : (840819179 : ℕ)^6063*100000000000000^5039 ≤ 5083772789411^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840819179 10000000000 5083772789411 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5199253043/10000000000 : ℝ), (5564374843/10000000000 : ℝ), (-840819179/10000000000 : ℝ)] ![(45521432206241/100000000000000 : ℝ), (24697397495483/50000000000000 : ℝ), (5083772789411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5199253043/10000000000 : ℝ)|^6063 ≤ (45521432206241/100000000000000 : ℝ)^5039
        have hw : |(5199253043/10000000000 : ℝ)|=(5199253043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5564374843/10000000000 : ℝ)|^6063 ≤ (24697397495483/50000000000000 : ℝ)^5039
        have hw : |(5564374843/10000000000 : ℝ)|=(5564374843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-840819179/10000000000 : ℝ)|^6063 ≤ (5083772789411/100000000000000 : ℝ)^5039
        have hw : |(-840819179/10000000000 : ℝ)|=(840819179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_s0_7 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1977668763/5000000000 : ℝ)*x 0 + (2492036487/5000000000 : ℝ)*x 1 + (95366523/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1977668763/5000000000 : ℝ)^6063 ≤ (32758592634503/100000000000000 : ℝ)^5039 := by
    have hnat : (1977668763 : ℕ)^6063*100000000000000^5039 ≤ 32758592634503^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1977668763 5000000000 32758592634503 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2492036487/5000000000 : ℝ)^6063 ≤ (43264234889821/100000000000000 : ℝ)^5039 := by
    have hnat : (2492036487 : ℕ)^6063*100000000000000^5039 ≤ 43264234889821^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2492036487 5000000000 43264234889821 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (95366523/312500000 : ℝ)^6063 ≤ (23977172465383/100000000000000 : ℝ)^5039 := by
    have hnat : (95366523 : ℕ)^6063*100000000000000^5039 ≤ 23977172465383^5039*312500000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95366523 312500000 23977172465383 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1977668763/5000000000 : ℝ), (2492036487/5000000000 : ℝ), (95366523/312500000 : ℝ)] ![(32758592634503/100000000000000 : ℝ), (43264234889821/100000000000000 : ℝ), (23977172465383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1977668763/5000000000 : ℝ)|^6063 ≤ (32758592634503/100000000000000 : ℝ)^5039
        have hw : |(1977668763/5000000000 : ℝ)|=(1977668763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2492036487/5000000000 : ℝ)|^6063 ≤ (43264234889821/100000000000000 : ℝ)^5039
        have hw : |(2492036487/5000000000 : ℝ)|=(2492036487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(95366523/312500000 : ℝ)|^6063 ≤ (23977172465383/100000000000000 : ℝ)^5039
        have hw : |(95366523/312500000 : ℝ)|=(95366523/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1768_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45278133/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (737/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19897/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (6047/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^6047 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^6047*1^1024 ≤ 0^1024*1^6047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 6047 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 6047 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (6047/1024 : ℝ) ≤ (446740614313014147/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^6047 ≤ (446740614313014147/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^6047*100000000000000000000^1024 ≤ 446740614313014147^1024*5^6047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 446740614313014147 100000000000000000000 6047 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (446740614313014147/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6047 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (6047/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^6047 := by
      have hnat : (1 : ℕ)^1024*1^6047 ≤ 1^6047*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 6047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 6047 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100446740614313014147/100000000000000000000 : ℝ) ≤ (10007551114573593/10000000000000000 : ℝ) ^ (6047/1024 : ℝ) := by
    have hpowers : (100446740614313014147/100000000000000000000 : ℝ)^1024 ≤ (10007551114573593/10000000000000000 : ℝ)^6047 := by
      have hnat : (100446740614313014147 : ℕ)^1024*10000000000000000^6047 ≤ 10007551114573593^6047*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100446740614313014147 100000000000000000000 10007551114573593 10000000000000000 1024 6047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10007551114573593/10000000000000000 : ℝ)) (X := (100446740614313014147/100000000000000000000 : ℝ)) (by norm_num) 6047 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50446740614313014147/50000000000000000000 : ℝ) ≤ (5007551114573593/5000000000000000 : ℝ) ^ (6047/1024 : ℝ) := by
    have hpowers : (50446740614313014147/50000000000000000000 : ℝ)^1024 ≤ (5007551114573593/5000000000000000 : ℝ)^6047 := by
      have hnat : (50446740614313014147 : ℕ)^1024*5000000000000000^6047 ≤ 5007551114573593^6047*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50446740614313014147 50000000000000000000 5007551114573593 5000000000000000 1024 6047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5007551114573593/5000000000000000 : ℝ)) (X := (50446740614313014147/50000000000000000000 : ℝ)) (by norm_num) 6047 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(7551114573593/4000000000000000 : ℝ)*(0 : ℝ))^(6047/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7551114573593/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(446740614313014147/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(7551114573593/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(6047/1024 : ℝ) := by
    rw [show (1 : ℝ)+(7551114573593/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10007551114573593/10000000000000000 : ℝ) by norm_num, show 1+(446740614313014147/100000000000000000000 : ℝ)+(0 : ℝ)=(100446740614313014147/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(446740614313014147/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(7551114573593/4000000000000000 : ℝ)*(2/5 : ℝ))^(6047/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(7551114573593/4000000000000000 : ℝ)*(2/5 : ℝ)=(5007551114573593/5000000000000000 : ℝ) by norm_num, show 1+2*(446740614313014147/100000000000000000000 : ℝ)=(50446740614313014147/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(7551114573593/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6047/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7551114573593/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(7551114573593/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6047/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7551114573593/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(7551114573593/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6047/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (7551114573593/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1095916867/10000000000 : ℝ)*X 0 0+(2789551211/5000000000 : ℝ)*X 0 1+(2501172091/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668973849/1250000000 : ℝ)*X 1 0+(-56113943/400000000 : ℝ)*X 1 1+(5002343621/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351787091/10000000000 : ℝ)*X 2 0+(125058653/250000000 : ℝ)*X 2 1+(-701425099/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((3951669777/10000000000 : ℝ)*X 0 0+(749943629/2500000000 : ℝ)*X 0 1+(314653979/625000000 : ℝ)*X 0 2+(3951669777/10000000000 : ℝ)*X 1 0+(749943629/2500000000 : ℝ)*X 1 1+(314653979/625000000 : ℝ)*X 1 2+(3951669777/10000000000 : ℝ)*X 2 0+(749943629/2500000000 : ℝ)*X 2 1+(314653979/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-8775661/80000000 : ℝ)*X 0 0+(200665167/400000000 : ℝ)*X 0 1+(111287499/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2599626359/5000000000 : ℝ)*X 1 0+(-168163899/2000000000 : ℝ)*X 1 1+(1391093737/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5199253043/10000000000 : ℝ)*X 2 0+(5564374843/10000000000 : ℝ)*X 2 1+(-840819179/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1977668763/5000000000 : ℝ)*X 0 0+(2492036487/5000000000 : ℝ)*X 0 1+(95366523/312500000 : ℝ)*X 0 2+(1977668763/5000000000 : ℝ)*X 1 0+(2492036487/5000000000 : ℝ)*X 1 1+(95366523/312500000 : ℝ)*X 1 2+(1977668763/5000000000 : ℝ)*X 2 0+(2492036487/5000000000 : ℝ)*X 2 1+(95366523/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (216975244437986861114301/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15926701/3125000000000 : ℝ)*(base1) + (490374639/25000000000000 : ℝ)*(base19) + (657009191/100000000000000 : ℝ)*(base23) + (445215933/100000000000000 : ℝ)*(upper3) + (556330076104481/50000000000000 : ℝ)*(major0) + (556330076104481/50000000000000 : ℝ)*(major1) + (556330076104481/50000000000000 : ℝ)*(major2) + (433459835514307/25000000000000 : ℝ)*(sp0) + (866920062217281/50000000000000 : ℝ)*(sp1) + (866918864360143/50000000000000 : ℝ)*(sp2) + (491475992829751/100000000000000 : ℝ)*(sp3) + (3253530321/100000000000000 : ℝ)*(sp4) + (92505091/2500000000000 : ℝ)*(sp6) + (356675073/25000000000000 : ℝ)*(sp7) + (19659117167379/4000000000000 : ℝ)*(f.failure) + (866921042966559/50000000000000 : ℝ)*(f.sum) + (10893250229767/100000000000000000000000000000 : ℝ)*base66 + (968353768570233/200000000000000000000000000000 : ℝ)*base67 + (1781611827170233/200000000000000000000000000000 : ℝ)*base69 + (218475586970233/200000000000000000000000000000 : ℝ)*base71 + (134376354170233/100000000000000000000000000000 : ℝ)*base73 + (218027315970233/200000000000000000000000000000 : ℝ)*base75 + (531245298570233/200000000000000000000000000000 : ℝ)*base77 + (1696894278770233/200000000000000000000000000000 : ℝ)*base79 + (200851792770233/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (23407/80000000000000000000 : ℝ)*base89 + (23407/80000000000000000000 : ℝ)*base91 + (23407/80000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3750043068188515803/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (4838237/1562500000000 : ℝ)*(base19) + (11606283/2500000000000 : ℝ)*(base23) + (32691801/25000000000000 : ℝ)*(base32) + (87936123/100000000000000 : ℝ)*(upper3) + (14787443/50000000000000 : ℝ)*(upper5) + (585792474982397/50000000000000 : ℝ)*(major0) + (585792474982397/50000000000000 : ℝ)*(major1) + (585792474982397/50000000000000 : ℝ)*(major2) + (174533397/20000000000000 : ℝ)*(sp1) + (22526143/1000000000000 : ℝ)*(sp2) + (182566391841909/10000000000000 : ℝ)*(sp4) + (228207842013117/12500000000000 : ℝ)*(sp5) + (1825661201553469/100000000000000 : ℝ)*(sp6) + (10350114514837/2000000000000 : ℝ)*(sp7) + (103501171301811/20000000000000 : ℝ)*(f.failure) + (182566391841909/10000000000000 : ℝ)*(f.sum) + (213582651042421/100000000000000000000000000000 : ℝ)*base65 + (400499693957579/200000000000000000000000000000 : ℝ)*base68 + (1821276583957579/200000000000000000000000000000 : ℝ)*base70 + (15213417557579/200000000000000000000000000000 : ℝ)*base72 + (313399015542421/100000000000000000000000000000 : ℝ)*base73 + (448363313442421/200000000000000000000000000000 : ℝ)*base75 + (361381277357579/200000000000000000000000000000 : ℝ)*base78 + (1176791182642421/200000000000000000000000000000 : ℝ)*base79 + (355255988857579/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (5598863/400000000000000000000 : ℝ)*base89 + (5598863/400000000000000000000 : ℝ)*base91 + (5598863/400000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1768_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45278133/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (737/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19897/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1768_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1768_s1_0 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-141038943/1250000000 : ℝ)*x 0 + (2737665099/5000000000 : ℝ)*x 1 + (5084240803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (141038943/1250000000 : ℝ)^6063 ≤ (3621082953041/50000000000000 : ℝ)^5039 := by
    have hnat : (141038943 : ℕ)^6063*50000000000000^5039 ≤ 3621082953041^5039*1250000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141038943 1250000000 3621082953041 50000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2737665099/5000000000 : ℝ)^6063 ≤ (242226353651/500000000000 : ℝ)^5039 := by
    have hnat : (2737665099 : ℕ)^6063*500000000000^5039 ≤ 242226353651^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2737665099 5000000000 242226353651 500000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5084240803/10000000000 : ℝ)^6063 ≤ (11078140838217/25000000000000 : ℝ)^5039 := by
    have hnat : (5084240803 : ℕ)^6063*25000000000000^5039 ≤ 11078140838217^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084240803 10000000000 11078140838217 25000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-141038943/1250000000 : ℝ), (2737665099/5000000000 : ℝ), (5084240803/10000000000 : ℝ)] ![(3621082953041/50000000000000 : ℝ), (242226353651/500000000000 : ℝ), (11078140838217/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-141038943/1250000000 : ℝ)|^6063 ≤ (3621082953041/50000000000000 : ℝ)^5039
        have hw : |(-141038943/1250000000 : ℝ)|=(141038943/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2737665099/5000000000 : ℝ)|^6063 ≤ (242226353651/500000000000 : ℝ)^5039
        have hw : |(2737665099/5000000000 : ℝ)|=(2737665099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5084240803/10000000000 : ℝ)|^6063 ≤ (11078140838217/25000000000000 : ℝ)^5039
        have hw : |(5084240803/10000000000 : ℝ)|=(5084240803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_s1_1 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5324287339/10000000000 : ℝ)*x 0 + (-1332350931/10000000000 : ℝ)*x 1 + (5084241161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5324287339/10000000000 : ℝ)^6063 ≤ (11710454272737/25000000000000 : ℝ)^5039 := by
    have hnat : (5324287339 : ℕ)^6063*25000000000000^5039 ≤ 11710454272737^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5324287339 10000000000 11710454272737 25000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1332350931/10000000000 : ℝ)^6063 ≤ (8845615782391/100000000000000 : ℝ)^5039 := by
    have hnat : (1332350931 : ℕ)^6063*100000000000000^5039 ≤ 8845615782391^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1332350931 10000000000 8845615782391 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5084241161/10000000000 : ℝ)^6063 ≤ (44312567107151/100000000000000 : ℝ)^5039 := by
    have hnat : (5084241161 : ℕ)^6063*100000000000000^5039 ≤ 44312567107151^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084241161 10000000000 44312567107151 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5324287339/10000000000 : ℝ), (-1332350931/10000000000 : ℝ), (5084241161/10000000000 : ℝ)] ![(11710454272737/25000000000000 : ℝ), (8845615782391/100000000000000 : ℝ), (44312567107151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5324287339/10000000000 : ℝ)|^6063 ≤ (11710454272737/25000000000000 : ℝ)^5039
        have hw : |(5324287339/10000000000 : ℝ)|=(5324287339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1332350931/10000000000 : ℝ)|^6063 ≤ (8845615782391/100000000000000 : ℝ)^5039
        have hw : |(-1332350931/10000000000 : ℝ)|=(1332350931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5084241161/10000000000 : ℝ)|^6063 ≤ (44312567107151/100000000000000 : ℝ)^5039
        have hw : |(5084241161/10000000000 : ℝ)|=(5084241161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_s1_2 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2662144129/5000000000 : ℝ)*x 0 + (5084240269/10000000000 : ℝ)*x 1 + (-266470177/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2662144129/5000000000 : ℝ)^6063 ≤ (23420913409557/50000000000000 : ℝ)^5039 := by
    have hnat : (2662144129 : ℕ)^6063*50000000000000^5039 ≤ 23420913409557^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2662144129 5000000000 23420913409557 50000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5084240269/10000000000 : ℝ)^6063 ≤ (5539069719113/12500000000000 : ℝ)^5039 := by
    have hnat : (5084240269 : ℕ)^6063*12500000000000^5039 ≤ 5539069719113^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084240269 10000000000 5539069719113 12500000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (266470177/2000000000 : ℝ)^6063 ≤ (8845615414931/100000000000000 : ℝ)^5039 := by
    have hnat : (266470177 : ℕ)^6063*100000000000000^5039 ≤ 8845615414931^5039*2000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      266470177 2000000000 8845615414931 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2662144129/5000000000 : ℝ), (5084240269/10000000000 : ℝ), (-266470177/2000000000 : ℝ)] ![(23420913409557/50000000000000 : ℝ), (5539069719113/12500000000000 : ℝ), (8845615414931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2662144129/5000000000 : ℝ)|^6063 ≤ (23420913409557/50000000000000 : ℝ)^5039
        have hw : |(2662144129/5000000000 : ℝ)|=(2662144129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5084240269/10000000000 : ℝ)|^6063 ≤ (5539069719113/12500000000000 : ℝ)^5039
        have hw : |(5084240269/10000000000 : ℝ)|=(5084240269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-266470177/2000000000 : ℝ)|^6063 ≤ (8845615414931/100000000000000 : ℝ)^5039
        have hw : |(-266470177/2000000000 : ℝ)|=(266470177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_s1_3 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3984884417/10000000000 : ℝ)*x 0 + (3325003573/10000000000 : ℝ)*x 1 + (4704698971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3984884417/10000000000 : ℝ)^6063 ≤ (1322130223803/4000000000000 : ℝ)^5039 := by
    have hnat : (3984884417 : ℕ)^6063*4000000000000^5039 ≤ 1322130223803^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3984884417 10000000000 1322130223803 4000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3325003573/10000000000 : ℝ)^6063 ≤ (13291779930007/50000000000000 : ℝ)^5039 := by
    have hnat : (3325003573 : ℕ)^6063*50000000000000^5039 ≤ 13291779930007^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3325003573 10000000000 13291779930007 50000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4704698971/10000000000 : ℝ)^6063 ≤ (20181592264817/50000000000000 : ℝ)^5039 := by
    have hnat : (4704698971 : ℕ)^6063*50000000000000^5039 ≤ 20181592264817^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4704698971 10000000000 20181592264817 50000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3984884417/10000000000 : ℝ), (3325003573/10000000000 : ℝ), (4704698971/10000000000 : ℝ)] ![(1322130223803/4000000000000 : ℝ), (13291779930007/50000000000000 : ℝ), (20181592264817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3984884417/10000000000 : ℝ)|^6063 ≤ (1322130223803/4000000000000 : ℝ)^5039
        have hw : |(3984884417/10000000000 : ℝ)|=(3984884417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3325003573/10000000000 : ℝ)|^6063 ≤ (13291779930007/50000000000000 : ℝ)^5039
        have hw : |(3325003573/10000000000 : ℝ)|=(3325003573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4704698971/10000000000 : ℝ)|^6063 ≤ (20181592264817/50000000000000 : ℝ)^5039
        have hw : |(4704698971/10000000000 : ℝ)|=(4704698971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_s1_4 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-141079301/1250000000 : ℝ)*x 0 + (636353801/1250000000 : ℝ)*x 1 + (5468603169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (141079301/1250000000 : ℝ)^6063 ≤ (7244659437799/100000000000000 : ℝ)^5039 := by
    have hnat : (141079301 : ℕ)^6063*100000000000000^5039 ≤ 7244659437799^5039*1250000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141079301 1250000000 7244659437799 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (636353801/1250000000 : ℝ)^6063 ≤ (11095419119203/25000000000000 : ℝ)^5039 := by
    have hnat : (636353801 : ℕ)^6063*25000000000000^5039 ≤ 11095419119203^5039*1250000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      636353801 1250000000 11095419119203 25000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5468603169/10000000000 : ℝ)^6063 ≤ (24186832041007/50000000000000 : ℝ)^5039 := by
    have hnat : (5468603169 : ℕ)^6063*50000000000000^5039 ≤ 24186832041007^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468603169 10000000000 24186832041007 50000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-141079301/1250000000 : ℝ), (636353801/1250000000 : ℝ), (5468603169/10000000000 : ℝ)] ![(7244659437799/100000000000000 : ℝ), (11095419119203/25000000000000 : ℝ), (24186832041007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-141079301/1250000000 : ℝ)|^6063 ≤ (7244659437799/100000000000000 : ℝ)^5039
        have hw : |(-141079301/1250000000 : ℝ)|=(141079301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(636353801/1250000000 : ℝ)|^6063 ≤ (11095419119203/25000000000000 : ℝ)^5039
        have hw : |(636353801/1250000000 : ℝ)|=(636353801/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5468603169/10000000000 : ℝ)|^6063 ≤ (24186832041007/50000000000000 : ℝ)^5039
        have hw : |(5468603169/10000000000 : ℝ)|=(5468603169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_s1_5 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5221239287/10000000000 : ℝ)*x 0 + (-947988439/10000000000 : ℝ)*x 1 + (109372057/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5221239287/10000000000 : ℝ)^6063 ≤ (22876573982439/50000000000000 : ℝ)^5039 := by
    have hnat : (5221239287 : ℕ)^6063*50000000000000^5039 ≤ 22876573982439^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221239287 10000000000 22876573982439 50000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (947988439/10000000000 : ℝ)^6063 ≤ (5873191332213/100000000000000 : ℝ)^5039 := by
    have hnat : (947988439 : ℕ)^6063*100000000000000^5039 ≤ 5873191332213^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947988439 10000000000 5873191332213 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109372057/200000000 : ℝ)^6063 ≤ (9674732137361/20000000000000 : ℝ)^5039 := by
    have hnat : (109372057 : ℕ)^6063*20000000000000^5039 ≤ 9674732137361^5039*200000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109372057 200000000 9674732137361 20000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5221239287/10000000000 : ℝ), (-947988439/10000000000 : ℝ), (109372057/200000000 : ℝ)] ![(22876573982439/50000000000000 : ℝ), (5873191332213/100000000000000 : ℝ), (9674732137361/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5221239287/10000000000 : ℝ)|^6063 ≤ (22876573982439/50000000000000 : ℝ)^5039
        have hw : |(5221239287/10000000000 : ℝ)|=(5221239287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-947988439/10000000000 : ℝ)|^6063 ≤ (5873191332213/100000000000000 : ℝ)^5039
        have hw : |(-947988439/10000000000 : ℝ)|=(947988439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(109372057/200000000 : ℝ)|^6063 ≤ (9674732137361/20000000000000 : ℝ)^5039
        have hw : |(109372057/200000000 : ℝ)|=(109372057/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_s1_6 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5221239483/10000000000 : ℝ)*x 0 + (1367150707/2500000000 : ℝ)*x 1 + (-947988193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5221239483/10000000000 : ℝ)^6063 ≤ (5719143753929/12500000000000 : ℝ)^5039 := by
    have hnat : (5221239483 : ℕ)^6063*12500000000000^5039 ≤ 5719143753929^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221239483 10000000000 5719143753929 12500000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367150707/2500000000 : ℝ)^6063 ≤ (48373660452653/100000000000000 : ℝ)^5039 := by
    have hnat : (1367150707 : ℕ)^6063*100000000000000^5039 ≤ 48373660452653^5039*2500000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367150707 2500000000 48373660452653 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (947988193/10000000000 : ℝ)^6063 ≤ (5873189498423/100000000000000 : ℝ)^5039 := by
    have hnat : (947988193 : ℕ)^6063*100000000000000^5039 ≤ 5873189498423^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947988193 10000000000 5873189498423 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5221239483/10000000000 : ℝ), (1367150707/2500000000 : ℝ), (-947988193/10000000000 : ℝ)] ![(5719143753929/12500000000000 : ℝ), (48373660452653/100000000000000 : ℝ), (5873189498423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5221239483/10000000000 : ℝ)|^6063 ≤ (5719143753929/12500000000000 : ℝ)^5039
        have hw : |(5221239483/10000000000 : ℝ)|=(5221239483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1367150707/2500000000 : ℝ)|^6063 ≤ (48373660452653/100000000000000 : ℝ)^5039
        have hw : |(1367150707/2500000000 : ℝ)|=(1367150707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-947988193/10000000000 : ℝ)|^6063 ≤ (5873189498423/100000000000000 : ℝ)^5039
        have hw : |(-947988193/10000000000 : ℝ)|=(947988193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_s1_7 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3986024331/10000000000 : ℝ)*x 0 + (117036263/250000000 : ℝ)*x 1 + (104648083/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3986024331/10000000000 : ℝ)^6063 ≤ (4133079070043/12500000000000 : ℝ)^5039 := by
    have hnat : (3986024331 : ℕ)^6063*12500000000000^5039 ≤ 4133079070043^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3986024331 10000000000 4133079070043 12500000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (117036263/250000000 : ℝ)^6063 ≤ (40123316473837/100000000000000 : ℝ)^5039 := by
    have hnat : (117036263 : ℕ)^6063*100000000000000^5039 ≤ 40123316473837^5039*250000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      117036263 250000000 40123316473837 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104648083/312500000 : ℝ)^6063 ≤ (26812050953247/100000000000000 : ℝ)^5039 := by
    have hnat : (104648083 : ℕ)^6063*100000000000000^5039 ≤ 26812050953247^5039*312500000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104648083 312500000 26812050953247 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3986024331/10000000000 : ℝ), (117036263/250000000 : ℝ), (104648083/312500000 : ℝ)] ![(4133079070043/12500000000000 : ℝ), (40123316473837/100000000000000 : ℝ), (26812050953247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3986024331/10000000000 : ℝ)|^6063 ≤ (4133079070043/12500000000000 : ℝ)^5039
        have hw : |(3986024331/10000000000 : ℝ)|=(3986024331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(117036263/250000000 : ℝ)|^6063 ≤ (40123316473837/100000000000000 : ℝ)^5039
        have hw : |(117036263/250000000 : ℝ)|=(117036263/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104648083/312500000 : ℝ)|^6063 ≤ (26812050953247/100000000000000 : ℝ)^5039
        have hw : |(104648083/312500000 : ℝ)|=(104648083/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1768_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45278133/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19897/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (737/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (4603/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17661/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19897/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (737/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19897/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (737/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19897/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (737/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19897/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (737/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19897/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (737/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19897/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (737/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (737/10000 : ℝ) ^ (6047/1024 : ℝ) ≤ (10257838170713/50000000000000000000 : ℝ) := by
    have hpowers : (737/10000 : ℝ)^6047 ≤ (10257838170713/50000000000000000000 : ℝ)^1024 := by
      have hnat : (737 : ℕ)^6047*50000000000000000000^1024 ≤ 10257838170713^1024*10000^6047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        737 10000 10257838170713 50000000000000000000 6047 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (737/10000 : ℝ)) (X := (10257838170713/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6047 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19897/100000 : ℝ) ^ (6047/1024 : ℝ) ≤ (7230178841864329/100000000000000000000 : ℝ) := by
    have hpowers : (19897/100000 : ℝ)^6047 ≤ (7230178841864329/100000000000000000000 : ℝ)^1024 := by
      have hnat : (19897 : ℕ)^6047*100000000000000000000^1024 ≤ 7230178841864329^1024*100000^6047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19897 100000 7230178841864329 100000000000000000000 6047 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19897/100000 : ℝ)) (X := (7230178841864329/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6047 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000010257838170713/25000000000000000000 : ℝ) ≤ (10000000694825501/10000000000000000 : ℝ) ^ (6047/1024 : ℝ) := by
    have hpowers : (25000010257838170713/25000000000000000000 : ℝ)^1024 ≤ (10000000694825501/10000000000000000 : ℝ)^6047 := by
      have hnat : (25000010257838170713 : ℕ)^1024*10000000000000000^6047 ≤ 10000000694825501^6047*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000010257838170713 25000000000000000000 10000000694825501 10000000000000000 1024 6047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000694825501/10000000000000000 : ℝ)) (X := (25000010257838170713/25000000000000000000 : ℝ)) (by norm_num) 6047 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20001450138903641151/20000000000000000000 : ℝ) ≤ (10000122779685903/10000000000000000 : ℝ) ^ (6047/1024 : ℝ) := by
    have hpowers : (20001450138903641151/20000000000000000000 : ℝ)^1024 ≤ (10000122779685903/10000000000000000 : ℝ)^6047 := by
      have hnat : (20001450138903641151 : ℕ)^1024*10000000000000000^6047 ≤ 10000122779685903^6047*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20001450138903641151 20000000000000000000 10000122779685903 10000000000000000 1024 6047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000122779685903/10000000000000000 : ℝ)) (X := (20001450138903641151/20000000000000000000 : ℝ)) (by norm_num) 6047 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50007230178841864329/50000000000000000000 : ℝ) ≤ (2000048972909261/2000000000000000 : ℝ) ^ (6047/1024 : ℝ) := by
    have hpowers : (50007230178841864329/50000000000000000000 : ℝ)^1024 ≤ (2000048972909261/2000000000000000 : ℝ)^6047 := by
      have hnat : (50007230178841864329 : ℕ)^1024*2000000000000000^6047 ≤ 2000048972909261^6047*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50007230178841864329 50000000000000000000 2000048972909261 2000000000000000 1024 6047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000048972909261/2000000000000000 : ℝ)) (X := (50007230178841864329/50000000000000000000 : ℝ)) (by norm_num) 6047 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10257838170713/50000000000000000000 : ℝ) ≤ ((125268209173236725547/125270000000000000000 : ℝ)+2*(61042430201/626350000000000 : ℝ)*(737/10000 : ℝ))^(6047/1024 : ℝ) := by
    rw [show (125268209173236725547/125270000000000000000 : ℝ)+2*(61042430201/626350000000000 : ℝ)*(737/10000 : ℝ)=(10000000694825501/10000000000000000 : ℝ) by norm_num, show 1+2*(10257838170713/50000000000000000000 : ℝ)=(25000010257838170713/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7230178841864329/100000000000000000000 : ℝ)+(10257838170713/50000000000000000000 : ℝ) ≤ ((125268209173236725547/125270000000000000000 : ℝ)+(61042430201/626350000000000 : ℝ)*((19897/100000 : ℝ)+(737/10000 : ℝ)))^(6047/1024 : ℝ) := by
    rw [show (125268209173236725547/125270000000000000000 : ℝ)+(61042430201/626350000000000 : ℝ)*((19897/100000 : ℝ)+(737/10000 : ℝ))=(10000122779685903/10000000000000000 : ℝ) by norm_num, show 1+(7230178841864329/100000000000000000000 : ℝ)+(10257838170713/50000000000000000000 : ℝ)=(20001450138903641151/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7230178841864329/100000000000000000000 : ℝ) ≤ ((125268209173236725547/125270000000000000000 : ℝ)+2*(61042430201/626350000000000 : ℝ)*(19897/100000 : ℝ))^(6047/1024 : ℝ) := by
    rw [show (125268209173236725547/125270000000000000000 : ℝ)+2*(61042430201/626350000000000 : ℝ)*(19897/100000 : ℝ)=(2000048972909261/2000000000000000 : ℝ) by norm_num, show 1+2*(7230178841864329/100000000000000000000 : ℝ)=(50007230178841864329/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (125268209173236725547/125270000000000000000 : ℝ)*(X 1 0+X 2 0)+(61042430201/626350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6047/1024 : ℝ)) (lo := (737/10000 : ℝ)) (hi := (19897/100000 : ℝ)) (c := (125268209173236725547/125270000000000000000 : ℝ)) (alpha := (61042430201/626350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (125268209173236725547/125270000000000000000 : ℝ)*(X 0 1+X 2 1)+(61042430201/626350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6047/1024 : ℝ)) (lo := (737/10000 : ℝ)) (hi := (19897/100000 : ℝ)) (c := (125268209173236725547/125270000000000000000 : ℝ)) (alpha := (61042430201/626350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (125268209173236725547/125270000000000000000 : ℝ)*(X 0 2+X 1 2)+(61042430201/626350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6047/1024 : ℝ)) (lo := (737/10000 : ℝ)) (hi := (19897/100000 : ℝ)) (c := (125268209173236725547/125270000000000000000 : ℝ)) (alpha := (61042430201/626350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-141038943/1250000000 : ℝ)*X 0 0+(2737665099/5000000000 : ℝ)*X 0 1+(5084240803/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5324287339/10000000000 : ℝ)*X 1 0+(-1332350931/10000000000 : ℝ)*X 1 1+(5084241161/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2662144129/5000000000 : ℝ)*X 2 0+(5084240269/10000000000 : ℝ)*X 2 1+(-266470177/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((3984884417/10000000000 : ℝ)*X 0 0+(3325003573/10000000000 : ℝ)*X 0 1+(4704698971/10000000000 : ℝ)*X 0 2+(3984884417/10000000000 : ℝ)*X 1 0+(3325003573/10000000000 : ℝ)*X 1 1+(4704698971/10000000000 : ℝ)*X 1 2+(3984884417/10000000000 : ℝ)*X 2 0+(3325003573/10000000000 : ℝ)*X 2 1+(4704698971/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-141079301/1250000000 : ℝ)*X 0 0+(636353801/1250000000 : ℝ)*X 0 1+(5468603169/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5221239287/10000000000 : ℝ)*X 1 0+(-947988439/10000000000 : ℝ)*X 1 1+(109372057/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5221239483/10000000000 : ℝ)*X 2 0+(1367150707/2500000000 : ℝ)*X 2 1+(-947988193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3986024331/10000000000 : ℝ)*X 0 0+(117036263/250000000 : ℝ)*X 0 1+(104648083/312500000 : ℝ)*X 0 2+(3986024331/10000000000 : ℝ)*X 1 0+(117036263/250000000 : ℝ)*X 1 1+(104648083/312500000 : ℝ)*X 1 2+(3986024331/10000000000 : ℝ)*X 2 0+(117036263/250000000 : ℝ)*X 2 1+(104648083/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10041598760796229620075557913/782937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (367775897/25000000000000 : ℝ)*(base19) + (951091359/50000000000000 : ℝ)*(base23) + (71669801/25000000000000 : ℝ)*(upper3) + (2733917/50000000000000 : ℝ)*(upper4) + (354229901/100000000000000 : ℝ)*(upper5) + (205112057718869/12500000000000 : ℝ)*(major0) + (205112057718869/12500000000000 : ℝ)*(major1) + (205112057718869/12500000000000 : ℝ)*(major2) + (2556971283813841/100000000000000 : ℝ)*(sp0) + (1278491775132523/50000000000000 : ℝ)*(sp1) + (639245779796479/25000000000000 : ℝ)*(sp2) + (724802477716033/100000000000000 : ℝ)*(sp3) + (6868777397/50000000000000 : ℝ)*(sp4) + (62461239/1250000000000 : ℝ)*(sp7) + (724807474615153/100000000000000 : ℝ)*(f.failure) + (1278492510684317/50000000000000 : ℝ)*(f.sum) + (99737334853171/62635000000000000000000000000 : ℝ)*base66 + (6546510082303421343/1565875000000000000000000000000000 : ℝ)*base67 + (3001515502577046343/1565875000000000000000000000000000 : ℝ)*base69 + (2128982075304421343/1565875000000000000000000000000000 : ℝ)*base71 + (219898060899999/62635000000000000000000000000 : ℝ)*base73 + (11324357379612171343/1565875000000000000000000000000000 : ℝ)*base75 + (13770132555077171343/1565875000000000000000000000000000 : ℝ)*base77 + (4157290281276171343/1565875000000000000000000000000000 : ℝ)*base79 + (124788152536299/62635000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (18650651/2000000000000000000000 : ℝ)*base90 + (18650651/2000000000000000000000 : ℝ)*base92 + (18650651/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (81354164438794065462987/31317500000000000000000000000 : ℝ) := by norm_num
    linear_combination (7035151/2500000000000 : ℝ)*(base19) + (58220703/12500000000000 : ℝ)*(base23) + (6746699/50000000000000 : ℝ)*(upper3) + (11166491/50000000000000 : ℝ)*(lower4) + (6294741/100000000000000 : ℝ)*(upper5) + (1698721893836771/100000000000000 : ℝ)*(major0) + (1698721893836771/100000000000000 : ℝ)*(major1) + (1698721893836771/100000000000000 : ℝ)*(major2) + (384801083/50000000000000 : ℝ)*(sp1) + (2908636039/100000000000000 : ℝ)*(sp2) + (2647093904709009/100000000000000 : ℝ)*(sp4) + (2647092853700803/100000000000000 : ℝ)*(sp5) + (1323545265153673/50000000000000 : ℝ)*(sp6) + (750349796373791/100000000000000 : ℝ)*(sp7) + (750349796373791/100000000000000 : ℝ)*(f.failure) + (2647093904709009/100000000000000 : ℝ)*(f.sum) + (204597679464327/62635000000000000000000000000 : ℝ)*base65 + (35260467703953888737/12527000000000000000000000000000000 : ℝ)*base67 + (6755684389021111263/12527000000000000000000000000000000 : ℝ)*base70 + (40708891383725888737/12527000000000000000000000000000000 : ℝ)*base71 + (185753243964747/62635000000000000000000000000 : ℝ)*base73 + (52664555757906111263/12527000000000000000000000000000000 : ℝ)*base76 + (57448276686789111263/12527000000000000000000000000000000 : ℝ)*base78 + (10400845317164888737/12527000000000000000000000000000000 : ℝ)*base79 + (12215092616963/62635000000000000000000000000 : ℝ)*base82 + (6612203/2000000000000000000000 : ℝ)*base89 + (6612203/2000000000000000000000 : ℝ)*base91 + (6612203/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1768_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45278133/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19897/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (737/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4603/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17661/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1768_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1768_s2_0 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-14109623/125000000 : ℝ)*x 0 + (5473852919/10000000000 : ℝ)*x 1 + (2542701453/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (14109623/125000000 : ℝ)^6063 ≤ (1449141088909/20000000000000 : ℝ)^5039 := by
    have hnat : (14109623 : ℕ)^6063*20000000000000^5039 ≤ 1449141088909^5039*125000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14109623 125000000 1449141088909 20000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5473852919/10000000000 : ℝ)^6063 ≤ (605369301601/1250000000000 : ℝ)^5039 := by
    have hnat : (5473852919 : ℕ)^6063*1250000000000^5039 ≤ 605369301601^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473852919 10000000000 605369301601 1250000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2542701453/5000000000 : ℝ)^6063 ≤ (2770296900331/6250000000000 : ℝ)^5039 := by
    have hnat : (2542701453 : ℕ)^6063*6250000000000^5039 ≤ 2770296900331^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542701453 5000000000 2770296900331 6250000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-14109623/125000000 : ℝ), (5473852919/10000000000 : ℝ), (2542701453/5000000000 : ℝ)] ![(1449141088909/20000000000000 : ℝ), (605369301601/1250000000000 : ℝ), (2770296900331/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-14109623/125000000 : ℝ)|^6063 ≤ (1449141088909/20000000000000 : ℝ)^5039
        have hw : |(-14109623/125000000 : ℝ)|=(14109623/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5473852919/10000000000 : ℝ)|^6063 ≤ (605369301601/1250000000000 : ℝ)^5039
        have hw : |(5473852919/10000000000 : ℝ)|=(5473852919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2542701453/5000000000 : ℝ)|^6063 ≤ (2770296900331/6250000000000 : ℝ)^5039
        have hw : |(2542701453/5000000000 : ℝ)|=(2542701453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_s2_1 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5323873267/10000000000 : ℝ)*x 0 + (-1331373743/10000000000 : ℝ)*x 1 + (2542701707/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5323873267/10000000000 : ℝ)^6063 ≤ (46837433925231/100000000000000 : ℝ)^5039 := by
    have hnat : (5323873267 : ℕ)^6063*100000000000000^5039 ≤ 46837433925231^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5323873267 10000000000 46837433925231 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1331373743/10000000000 : ℝ)^6063 ≤ (2209452581037/25000000000000 : ℝ)^5039 := by
    have hnat : (1331373743 : ℕ)^6063*25000000000000^5039 ≤ 2209452581037^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1331373743 10000000000 2209452581037 25000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2542701707/5000000000 : ℝ)^6063 ≤ (886495114657/2000000000000 : ℝ)^5039 := by
    have hnat : (2542701707 : ℕ)^6063*2000000000000^5039 ≤ 886495114657^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542701707 5000000000 886495114657 2000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5323873267/10000000000 : ℝ), (-1331373743/10000000000 : ℝ), (2542701707/5000000000 : ℝ)] ![(46837433925231/100000000000000 : ℝ), (2209452581037/25000000000000 : ℝ), (886495114657/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5323873267/10000000000 : ℝ)|^6063 ≤ (46837433925231/100000000000000 : ℝ)^5039
        have hw : |(5323873267/10000000000 : ℝ)|=(5323873267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1331373743/10000000000 : ℝ)|^6063 ≤ (2209452581037/25000000000000 : ℝ)^5039
        have hw : |(-1331373743/10000000000 : ℝ)|=(1331373743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2542701707/5000000000 : ℝ)|^6063 ≤ (886495114657/2000000000000 : ℝ)^5039
        have hw : |(2542701707/5000000000 : ℝ)|=(2542701707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_s2_2 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2661936533/5000000000 : ℝ)*x 0 + (5085403011/10000000000 : ℝ)*x 1 + (-1331374539/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2661936533/5000000000 : ℝ)^6063 ≤ (46837431797559/100000000000000 : ℝ)^5039 := by
    have hnat : (2661936533 : ℕ)^6063*100000000000000^5039 ≤ 46837431797559^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2661936533 5000000000 46837431797559 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5085403011/10000000000 : ℝ)^6063 ≤ (44324751506463/100000000000000 : ℝ)^5039 := by
    have hnat : (5085403011 : ℕ)^6063*100000000000000^5039 ≤ 44324751506463^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5085403011 10000000000 44324751506463 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1331374539/10000000000 : ℝ)^6063 ≤ (8837816681863/100000000000000 : ℝ)^5039 := by
    have hnat : (1331374539 : ℕ)^6063*100000000000000^5039 ≤ 8837816681863^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1331374539 10000000000 8837816681863 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2661936533/5000000000 : ℝ), (5085403011/10000000000 : ℝ), (-1331374539/10000000000 : ℝ)] ![(46837431797559/100000000000000 : ℝ), (44324751506463/100000000000000 : ℝ), (8837816681863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2661936533/5000000000 : ℝ)|^6063 ≤ (46837431797559/100000000000000 : ℝ)^5039
        have hw : |(2661936533/5000000000 : ℝ)|=(2661936533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5085403011/10000000000 : ℝ)|^6063 ≤ (44324751506463/100000000000000 : ℝ)^5039
        have hw : |(5085403011/10000000000 : ℝ)|=(5085403011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1331374539/10000000000 : ℝ)|^6063 ≤ (8837816681863/100000000000000 : ℝ)^5039
        have hw : |(-1331374539/10000000000 : ℝ)|=(1331374539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_s2_3 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3985263521/10000000000 : ℝ)*x 0 + (83240921/250000000 : ℝ)*x 1 + (940002727/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3985263521/10000000000 : ℝ)^6063 ≤ (33057039186979/100000000000000 : ℝ)^5039 := by
    have hnat : (3985263521 : ℕ)^6063*100000000000000^5039 ≤ 33057039186979^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3985263521 10000000000 33057039186979 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (83240921/250000000 : ℝ)^6063 ≤ (6657034271067/25000000000000 : ℝ)^5039 := by
    have hnat : (83240921 : ℕ)^6063*25000000000000^5039 ≤ 6657034271067^5039*250000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83240921 250000000 6657034271067 25000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (940002727/2000000000 : ℝ)^6063 ≤ (5039352964847/12500000000000 : ℝ)^5039 := by
    have hnat : (940002727 : ℕ)^6063*12500000000000^5039 ≤ 5039352964847^5039*2000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940002727 2000000000 5039352964847 12500000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3985263521/10000000000 : ℝ), (83240921/250000000 : ℝ), (940002727/2000000000 : ℝ)] ![(33057039186979/100000000000000 : ℝ), (6657034271067/25000000000000 : ℝ), (5039352964847/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3985263521/10000000000 : ℝ)|^6063 ≤ (33057039186979/100000000000000 : ℝ)^5039
        have hw : |(3985263521/10000000000 : ℝ)|=(3985263521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(83240921/250000000 : ℝ)|^6063 ≤ (6657034271067/25000000000000 : ℝ)^5039
        have hw : |(83240921/250000000 : ℝ)|=(83240921/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(940002727/2000000000 : ℝ)|^6063 ≤ (5039352964847/12500000000000 : ℝ)^5039
        have hw : |(940002727/2000000000 : ℝ)|=(940002727/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_s2_4 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-564543307/5000000000 : ℝ)*x 0 + (5091904563/10000000000 : ℝ)*x 1 + (2733608153/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (564543307/5000000000 : ℝ)^6063 ≤ (7248152142727/100000000000000 : ℝ)^5039 := by
    have hnat : (564543307 : ℕ)^6063*100000000000000^5039 ≤ 7248152142727^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564543307 5000000000 7248152142727 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5091904563/10000000000 : ℝ)^6063 ≤ (44392944157943/100000000000000 : ℝ)^5039 := by
    have hnat : (5091904563 : ℕ)^6063*100000000000000^5039 ≤ 44392944157943^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5091904563 10000000000 44392944157943 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2733608153/5000000000 : ℝ)^6063 ≤ (24179451840537/50000000000000 : ℝ)^5039 := by
    have hnat : (2733608153 : ℕ)^6063*50000000000000^5039 ≤ 24179451840537^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733608153 5000000000 24179451840537 50000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-564543307/5000000000 : ℝ), (5091904563/10000000000 : ℝ), (2733608153/5000000000 : ℝ)] ![(7248152142727/100000000000000 : ℝ), (44392944157943/100000000000000 : ℝ), (24179451840537/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-564543307/5000000000 : ℝ)|^6063 ≤ (7248152142727/100000000000000 : ℝ)^5039
        have hw : |(-564543307/5000000000 : ℝ)|=(564543307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5091904563/10000000000 : ℝ)|^6063 ≤ (44392944157943/100000000000000 : ℝ)^5039
        have hw : |(5091904563/10000000000 : ℝ)|=(5091904563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2733608153/5000000000 : ℝ)|^6063 ≤ (24179451840537/50000000000000 : ℝ)^5039
        have hw : |(2733608153/5000000000 : ℝ)|=(2733608153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_s2_5 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (522152671/1000000000 : ℝ)*x 0 + (-474780633/5000000000 : ℝ)*x 1 + (2733608153/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522152671/1000000000 : ℝ)^6063 ≤ (11439044616659/25000000000000 : ℝ)^5039 := by
    have hnat : (522152671 : ℕ)^6063*25000000000000^5039 ≤ 11439044616659^5039*1000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522152671 1000000000 11439044616659 25000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (474780633/5000000000 : ℝ)^6063 ≤ (1471229458327/25000000000000 : ℝ)^5039 := by
    have hnat : (474780633 : ℕ)^6063*25000000000000^5039 ≤ 1471229458327^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474780633 5000000000 1471229458327 25000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2733608153/5000000000 : ℝ)^6063 ≤ (24179451840537/50000000000000 : ℝ)^5039 := by
    have hnat : (2733608153 : ℕ)^6063*50000000000000^5039 ≤ 24179451840537^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733608153 5000000000 24179451840537 50000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(522152671/1000000000 : ℝ), (-474780633/5000000000 : ℝ), (2733608153/5000000000 : ℝ)] ![(11439044616659/25000000000000 : ℝ), (1471229458327/25000000000000 : ℝ), (24179451840537/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(522152671/1000000000 : ℝ)|^6063 ≤ (11439044616659/25000000000000 : ℝ)^5039
        have hw : |(522152671/1000000000 : ℝ)|=(522152671/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-474780633/5000000000 : ℝ)|^6063 ≤ (1471229458327/25000000000000 : ℝ)^5039
        have hw : |(-474780633/5000000000 : ℝ)|=(474780633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2733608153/5000000000 : ℝ)|^6063 ≤ (24179451840537/50000000000000 : ℝ)^5039
        have hw : |(2733608153/5000000000 : ℝ)|=(2733608153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_s2_6 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (522152671/1000000000 : ℝ)*x 0 + (2733608153/5000000000 : ℝ)*x 1 + (-474780633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522152671/1000000000 : ℝ)^6063 ≤ (11439044616659/25000000000000 : ℝ)^5039 := by
    have hnat : (522152671 : ℕ)^6063*25000000000000^5039 ≤ 11439044616659^5039*1000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522152671 1000000000 11439044616659 25000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2733608153/5000000000 : ℝ)^6063 ≤ (24179451840537/50000000000000 : ℝ)^5039 := by
    have hnat : (2733608153 : ℕ)^6063*50000000000000^5039 ≤ 24179451840537^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733608153 5000000000 24179451840537 50000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (474780633/5000000000 : ℝ)^6063 ≤ (1471229458327/25000000000000 : ℝ)^5039 := by
    have hnat : (474780633 : ℕ)^6063*25000000000000^5039 ≤ 1471229458327^5039*5000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474780633 5000000000 1471229458327 25000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(522152671/1000000000 : ℝ), (2733608153/5000000000 : ℝ), (-474780633/5000000000 : ℝ)] ![(11439044616659/25000000000000 : ℝ), (24179451840537/50000000000000 : ℝ), (1471229458327/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(522152671/1000000000 : ℝ)|^6063 ≤ (11439044616659/25000000000000 : ℝ)^5039
        have hw : |(522152671/1000000000 : ℝ)|=(522152671/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2733608153/5000000000 : ℝ)|^6063 ≤ (24179451840537/50000000000000 : ℝ)^5039
        have hw : |(2733608153/5000000000 : ℝ)|=(2733608153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-474780633/5000000000 : ℝ)|^6063 ≤ (1471229458327/25000000000000 : ℝ)^5039
        have hw : |(-474780633/5000000000 : ℝ)|=(474780633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1768_s2_7 (p : ℝ) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3986380581/10000000000 : ℝ)*x 0 + (4677078431/10000000000 : ℝ)*x 1 + (3353048673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3986380581/10000000000 : ℝ)^6063 ≤ (33068188265833/100000000000000 : ℝ)^5039 := by
    have hnat : (3986380581 : ℕ)^6063*100000000000000^5039 ≤ 33068188265833^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3986380581 10000000000 33068188265833 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4677078431/10000000000 : ℝ)^6063 ≤ (40078234038751/100000000000000 : ℝ)^5039 := by
    have hnat : (4677078431 : ℕ)^6063*100000000000000^5039 ≤ 40078234038751^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4677078431 10000000000 40078234038751 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3353048673/10000000000 : ℝ)^6063 ≤ (26853577684303/100000000000000 : ℝ)^5039 := by
    have hnat : (3353048673 : ℕ)^6063*100000000000000^5039 ≤ 26853577684303^5039*10000000000^6063 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3353048673 10000000000 26853577684303 100000000000000 6063 5039 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (6063/1024 : ℝ)) 6063 5039 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3986380581/10000000000 : ℝ), (4677078431/10000000000 : ℝ), (3353048673/10000000000 : ℝ)] ![(33068188265833/100000000000000 : ℝ), (40078234038751/100000000000000 : ℝ), (26853577684303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3986380581/10000000000 : ℝ)|^6063 ≤ (33068188265833/100000000000000 : ℝ)^5039
        have hw : |(3986380581/10000000000 : ℝ)|=(3986380581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4677078431/10000000000 : ℝ)|^6063 ≤ (40078234038751/100000000000000 : ℝ)^5039
        have hw : |(4677078431/10000000000 : ℝ)|=(4677078431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3353048673/10000000000 : ℝ)|^6063 ≤ (26853577684303/100000000000000 : ℝ)^5039
        have hw : |(3353048673/10000000000 : ℝ)|=(3353048673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1768_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45278133/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17661/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4603/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (577/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1763/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17661/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4603/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17661/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4603/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17661/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4603/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17661/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4603/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17661/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4603/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17661/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4603/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4603/50000 : ℝ) ^ (6047/1024 : ℝ) ≤ (76305495931327/100000000000000000000 : ℝ) := by
    have hpowers : (4603/50000 : ℝ)^6047 ≤ (76305495931327/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4603 : ℕ)^6047*100000000000000000000^1024 ≤ 76305495931327^1024*50000^6047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4603 50000 76305495931327 100000000000000000000 6047 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4603/50000 : ℝ)) (X := (76305495931327/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6047 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17661/100000 : ℝ) ^ (6047/1024 : ℝ) ≤ (3576180216564229/100000000000000000000 : ℝ) := by
    have hpowers : (17661/100000 : ℝ)^6047 ≤ (3576180216564229/100000000000000000000 : ℝ)^1024 := by
      have hnat : (17661 : ℕ)^6047*100000000000000000000^1024 ≤ 3576180216564229^1024*100000^6047 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17661 100000 3576180216564229 100000000000000000000 6047 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17661/100000 : ℝ)) (X := (3576180216564229/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 6047 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000076305495931327/50000000000000000000 : ℝ) ≤ (10000002584315473/10000000000000000 : ℝ) ^ (6047/1024 : ℝ) := by
    have hpowers : (50000076305495931327/50000000000000000000 : ℝ)^1024 ≤ (10000002584315473/10000000000000000 : ℝ)^6047 := by
      have hnat : (50000076305495931327 : ℕ)^1024*10000000000000000^6047 ≤ 10000002584315473^6047*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000076305495931327 50000000000000000000 10000002584315473 10000000000000000 1024 6047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000002584315473/10000000000000000 : ℝ)) (X := (50000076305495931327/50000000000000000000 : ℝ)) (by norm_num) 6047 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25000913121428123889/25000000000000000000 : ℝ) ≤ (10000061850316411/10000000000000000 : ℝ) ^ (6047/1024 : ℝ) := by
    have hpowers : (25000913121428123889/25000000000000000000 : ℝ)^1024 ≤ (10000061850316411/10000000000000000 : ℝ)^6047 := by
      have hnat : (25000913121428123889 : ℕ)^1024*10000000000000000^6047 ≤ 10000061850316411^6047*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000913121428123889 25000000000000000000 10000061850316411 10000000000000000 1024 6047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000061850316411/10000000000000000 : ℝ)) (X := (25000913121428123889/25000000000000000000 : ℝ)) (by norm_num) 6047 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50003576180216564229/50000000000000000000 : ℝ) ≤ (10000121116317349/10000000000000000 : ℝ) ^ (6047/1024 : ℝ) := by
    have hpowers : (50003576180216564229/50000000000000000000 : ℝ)^1024 ≤ (10000121116317349/10000000000000000 : ℝ)^6047 := by
      have hnat : (50003576180216564229 : ℕ)^1024*10000000000000000^6047 ≤ 10000121116317349^6047*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50003576180216564229 50000000000000000000 10000121116317349 10000000000000000 1024 6047 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000121116317349/10000000000000000 : ℝ)) (X := (50003576180216564229/50000000000000000000 : ℝ)) (by norm_num) 6047 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(76305495931327/100000000000000000000 : ℝ) ≤ ((84548930644778053759/84550000000000000000 : ℝ)+2*(29633000469/422750000000000 : ℝ)*(4603/50000 : ℝ))^(6047/1024 : ℝ) := by
    rw [show (84548930644778053759/84550000000000000000 : ℝ)+2*(29633000469/422750000000000 : ℝ)*(4603/50000 : ℝ)=(10000002584315473/10000000000000000 : ℝ) by norm_num, show 1+2*(76305495931327/100000000000000000000 : ℝ)=(50000076305495931327/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3576180216564229/100000000000000000000 : ℝ)+(76305495931327/100000000000000000000 : ℝ) ≤ ((84548930644778053759/84550000000000000000 : ℝ)+(29633000469/422750000000000 : ℝ)*((17661/100000 : ℝ)+(4603/50000 : ℝ)))^(6047/1024 : ℝ) := by
    rw [show (84548930644778053759/84550000000000000000 : ℝ)+(29633000469/422750000000000 : ℝ)*((17661/100000 : ℝ)+(4603/50000 : ℝ))=(10000061850316411/10000000000000000 : ℝ) by norm_num, show 1+(3576180216564229/100000000000000000000 : ℝ)+(76305495931327/100000000000000000000 : ℝ)=(25000913121428123889/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3576180216564229/100000000000000000000 : ℝ) ≤ ((84548930644778053759/84550000000000000000 : ℝ)+2*(29633000469/422750000000000 : ℝ)*(17661/100000 : ℝ))^(6047/1024 : ℝ) := by
    rw [show (84548930644778053759/84550000000000000000 : ℝ)+2*(29633000469/422750000000000 : ℝ)*(17661/100000 : ℝ)=(10000121116317349/10000000000000000 : ℝ) by norm_num, show 1+2*(3576180216564229/100000000000000000000 : ℝ)=(50003576180216564229/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (84548930644778053759/84550000000000000000 : ℝ)*(X 1 0+X 2 0)+(29633000469/422750000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6047/1024 : ℝ)) (lo := (4603/50000 : ℝ)) (hi := (17661/100000 : ℝ)) (c := (84548930644778053759/84550000000000000000 : ℝ)) (alpha := (29633000469/422750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (84548930644778053759/84550000000000000000 : ℝ)*(X 0 1+X 2 1)+(29633000469/422750000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6047/1024 : ℝ)) (lo := (4603/50000 : ℝ)) (hi := (17661/100000 : ℝ)) (c := (84548930644778053759/84550000000000000000 : ℝ)) (alpha := (29633000469/422750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (84548930644778053759/84550000000000000000 : ℝ)*(X 0 2+X 1 2)+(29633000469/422750000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (6047/1024 : ℝ)) (lo := (4603/50000 : ℝ)) (hi := (17661/100000 : ℝ)) (c := (84548930644778053759/84550000000000000000 : ℝ)) (alpha := (29633000469/422750000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-14109623/125000000 : ℝ)*X 0 0+(5473852919/10000000000 : ℝ)*X 0 1+(2542701453/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5323873267/10000000000 : ℝ)*X 1 0+(-1331373743/10000000000 : ℝ)*X 1 1+(2542701707/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2661936533/5000000000 : ℝ)*X 2 0+(5085403011/10000000000 : ℝ)*X 2 1+(-1331374539/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((3985263521/10000000000 : ℝ)*X 0 0+(83240921/250000000 : ℝ)*X 0 1+(940002727/2000000000 : ℝ)*X 0 2+(3985263521/10000000000 : ℝ)*X 1 0+(83240921/250000000 : ℝ)*X 1 1+(940002727/2000000000 : ℝ)*X 1 2+(3985263521/10000000000 : ℝ)*X 2 0+(83240921/250000000 : ℝ)*X 2 1+(940002727/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-564543307/5000000000 : ℝ)*X 0 0+(5091904563/10000000000 : ℝ)*X 0 1+(2733608153/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((522152671/1000000000 : ℝ)*X 1 0+(-474780633/5000000000 : ℝ)*X 1 1+(2733608153/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((522152671/1000000000 : ℝ)*X 2 0+(2733608153/5000000000 : ℝ)*X 2 1+(-474780633/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3986380581/10000000000 : ℝ)*X 0 0+(4677078431/10000000000 : ℝ)*X 0 1+(3353048673/10000000000 : ℝ)*X 0 2+(3986380581/10000000000 : ℝ)*X 1 0+(4677078431/10000000000 : ℝ)*X 1 1+(3353048673/10000000000 : ℝ)*X 1 2+(3986380581/10000000000 : ℝ)*X 2 0+(4677078431/10000000000 : ℝ)*X 2 1+(3353048673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1768_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (116958096350992305858261/10568750000000000000000000000 : ℝ) := by norm_num
    linear_combination (871595967/50000000000000 : ℝ)*(base19) + (1555443849/100000000000000 : ℝ)*(base23) + (61790231/100000000000000 : ℝ)*(lower2) + (511902057/100000000000000 : ℝ)*(upper3) + (1697533/12500000000000 : ℝ)*(lower4) + (826025304366823/50000000000000 : ℝ)*(major0) + (826025304366823/50000000000000 : ℝ)*(major1) + (826025304366823/50000000000000 : ℝ)*(major2) + (257435397152097/10000000000000 : ℝ)*(sp0) + (643591171065883/25000000000000 : ℝ)*(sp1) + (80448902250363/3125000000000 : ℝ)*(sp2) + (364864624264413/50000000000000 : ℝ)*(sp3) + (12455934497/100000000000000 : ℝ)*(sp4) + (5172602737/100000000000000 : ℝ)*(sp7) + (729734421131563/100000000000000 : ℝ)*(f.failure) + (1287183213727733/50000000000000 : ℝ)*(f.sum) + (163503124479073/42275000000000000000000000000 : ℝ)*base65 + (10717376371872562343/4227500000000000000000000000000000 : ℝ)*base68 + (21382812192710062343/4227500000000000000000000000000000 : ℝ)*base70 + (20682511526704937657/4227500000000000000000000000000000 : ℝ)*base71 + (27437688885077/42275000000000000000000000000 : ℝ)*base74 + (9394684757925062343/4227500000000000000000000000000000 : ℝ)*base76 + (37323069226974937657/4227500000000000000000000000000000 : ℝ)*base77 + (50895246331414937657/4227500000000000000000000000000000 : ℝ)*base79 + (174611349052977/42275000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (11879/2000000000000000000000 : ℝ)*base89 + (11879/2000000000000000000000 : ℝ)*base91 + (11879/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5893478709617651835646609737/528437500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (694928399/50000000000000 : ℝ)*(base19) + (185548641/12500000000000 : ℝ)*(base23) + (608551/156250000000 : ℝ)*(lower1) + (240519383/100000000000000 : ℝ)*(upper3) + (20995283/50000000000000 : ℝ)*(lower4) + (57996319/25000000000000 : ℝ)*(upper5) + (427463505449481/25000000000000 : ℝ)*(major0) + (427463505449481/25000000000000 : ℝ)*(major1) + (427463505449481/25000000000000 : ℝ)*(major2) + (720078817/100000000000000 : ℝ)*(sp2) + (532888131013577/20000000000000 : ℝ)*(sp4) + (2664439265211087/100000000000000 : ℝ)*(sp5) + (133221922529997/5000000000000 : ℝ)*(sp6) + (377633508386471/50000000000000 : ℝ)*(sp7) + (377633508386471/50000000000000 : ℝ)*(f.failure) + (532888131013577/20000000000000 : ℝ)*(f.sum) + (13961609376693/2642187500000000000000000000 : ℝ)*base66 + (17775287410989300921/2113750000000000000000000000000000 : ℝ)*base68 + (19461564276775550921/2113750000000000000000000000000000 : ℝ)*base70 + (21170345355054449079/2113750000000000000000000000000000 : ℝ)*base71 + (10014101394697/10568750000000000000000000000 : ℝ)*base74 + (21510743044390550921/2113750000000000000000000000000000 : ℝ)*base76 + (14550352494235550921/2113750000000000000000000000000000 : ℝ)*base78 + (15394106547304300921/2113750000000000000000000000000000 : ℝ)*base80 + (15798013376887/42275000000000000000000000000 : ℝ)*base81 + (9338643/1000000000000000000000 : ℝ)*base89 + (9338643/1000000000000000000000 : ℝ)*base91 + (9338643/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1768_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45278133/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17661/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4603/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (577/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1763/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1768_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1768_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45278133/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (577/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1763/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1768_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1768_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1768_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (6047/1024 : ℝ) ≤ p) (hpb : p ≤ (6063/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (45278133/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (577/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1763/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1768_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
