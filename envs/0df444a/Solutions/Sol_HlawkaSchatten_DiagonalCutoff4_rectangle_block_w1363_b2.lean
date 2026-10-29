-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1363_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:18:43.157593+00:00
-- url     : https://prove2.me/submissions/4cb0c193-cfeb-4f23-92fd-72749d8d818b

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
theorem support_rectangle_w1363_s6_0 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-506490933/2500000000 : ℝ)*x 0 + (5411634547/10000000000 : ℝ)*x 1 + (1311305453/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (506490933/2500000000 : ℝ)^4323 ≤ (308568906999/2500000000000 : ℝ)^3299 := by
    have hnat : (506490933 : ℕ)^4323*2500000000000^3299 ≤ 308568906999^3299*2500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506490933 2500000000 308568906999 2500000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411634547/10000000000 : ℝ)^4323 ≤ (44725416209747/100000000000000 : ℝ)^3299 := by
    have hnat : (5411634547 : ℕ)^4323*100000000000000^3299 ≤ 44725416209747^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411634547 10000000000 44725416209747 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311305453/2500000000 : ℝ)^4323 ≤ (10732956875107/25000000000000 : ℝ)^3299 := by
    have hnat : (1311305453 : ℕ)^4323*25000000000000^3299 ≤ 10732956875107^3299*2500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311305453 2500000000 10732956875107 25000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-506490933/2500000000 : ℝ), (5411634547/10000000000 : ℝ), (1311305453/2500000000 : ℝ)] ![(308568906999/2500000000000 : ℝ), (44725416209747/100000000000000 : ℝ), (10732956875107/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-506490933/2500000000 : ℝ)|^4323 ≤ (308568906999/2500000000000 : ℝ)^3299
        have hw : |(-506490933/2500000000 : ℝ)|=(506490933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411634547/10000000000 : ℝ)|^4323 ≤ (44725416209747/100000000000000 : ℝ)^3299
        have hw : |(5411634547/10000000000 : ℝ)|=(5411634547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311305453/2500000000 : ℝ)|^4323 ≤ (10732956875107/25000000000000 : ℝ)^3299
        have hw : |(1311305453/2500000000 : ℝ)|=(1311305453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s6_1 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334289297/625000000 : ℝ)*x 0 + (-65960501/312500000 : ℝ)*x 1 + (5245221771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334289297/625000000 : ℝ)^4323 ≤ (550553738847/1250000000000 : ℝ)^3299 := by
    have hnat : (334289297 : ℕ)^4323*1250000000000^3299 ≤ 550553738847^3299*625000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334289297 625000000 550553738847 1250000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65960501/312500000 : ℝ)^4323 ≤ (3255968454133/25000000000000 : ℝ)^3299 := by
    have hnat : (65960501 : ℕ)^4323*25000000000000^3299 ≤ 3255968454133^3299*312500000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65960501 312500000 3255968454133 25000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245221771/10000000000 : ℝ)^4323 ≤ (21465913530341/50000000000000 : ℝ)^3299 := by
    have hnat : (5245221771 : ℕ)^4323*50000000000000^3299 ≤ 21465913530341^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245221771 10000000000 21465913530341 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334289297/625000000 : ℝ), (-65960501/312500000 : ℝ), (5245221771/10000000000 : ℝ)] ![(550553738847/1250000000000 : ℝ), (3255968454133/25000000000000 : ℝ), (21465913530341/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334289297/625000000 : ℝ)|^4323 ≤ (550553738847/1250000000000 : ℝ)^3299
        have hw : |(334289297/625000000 : ℝ)|=(334289297/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-65960501/312500000 : ℝ)|^4323 ≤ (3255968454133/25000000000000 : ℝ)^3299
        have hw : |(-65960501/312500000 : ℝ)|=(65960501/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245221771/10000000000 : ℝ)|^4323 ≤ (21465913530341/50000000000000 : ℝ)^3299
        have hw : |(5245221771/10000000000 : ℝ)|=(5245221771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s6_2 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069725753/2000000000 : ℝ)*x 0 + (5245221787/10000000000 : ℝ)*x 1 + (-2110735993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069725753/2000000000 : ℝ)^4323 ≤ (1101107481201/2500000000000 : ℝ)^3299 := by
    have hnat : (1069725753 : ℕ)^4323*2500000000000^3299 ≤ 1101107481201^3299*2000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069725753 2000000000 1101107481201 2500000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245221787/10000000000 : ℝ)^4323 ≤ (4293182723229/10000000000000 : ℝ)^3299 := by
    have hnat : (5245221787 : ℕ)^4323*10000000000000^3299 ≤ 4293182723229^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245221787 10000000000 4293182723229 10000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2110735993/10000000000 : ℝ)^4323 ≤ (3255968375299/25000000000000 : ℝ)^3299 := by
    have hnat : (2110735993 : ℕ)^4323*25000000000000^3299 ≤ 3255968375299^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110735993 10000000000 3255968375299 25000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069725753/2000000000 : ℝ), (5245221787/10000000000 : ℝ), (-2110735993/10000000000 : ℝ)] ![(1101107481201/2500000000000 : ℝ), (4293182723229/10000000000000 : ℝ), (3255968375299/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069725753/2000000000 : ℝ)|^4323 ≤ (1101107481201/2500000000000 : ℝ)^3299
        have hw : |(1069725753/2000000000 : ℝ)|=(1069725753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245221787/10000000000 : ℝ)|^4323 ≤ (4293182723229/10000000000000 : ℝ)^3299
        have hw : |(5245221787/10000000000 : ℝ)|=(5245221787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2110735993/10000000000 : ℝ)|^4323 ≤ (3255968375299/25000000000000 : ℝ)^3299
        have hw : |(-2110735993/10000000000 : ℝ)|=(2110735993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s6_3 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2160578511/5000000000 : ℝ)*x 0 + (1037200751/2500000000 : ℝ)*x 1 + (4500122693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160578511/5000000000 : ℝ)^4323 ≤ (33303613920583/100000000000000 : ℝ)^3299 := by
    have hnat : (2160578511 : ℕ)^4323*100000000000000^3299 ≤ 33303613920583^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160578511 5000000000 33303613920583 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037200751/2500000000 : ℝ)^4323 ≤ (7893455697709/25000000000000 : ℝ)^3299 := by
    have hnat : (1037200751 : ℕ)^4323*25000000000000^3299 ≤ 7893455697709^3299*2500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037200751 2500000000 7893455697709 25000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4500122693/10000000000 : ℝ)^4323 ≤ (35122563269429/100000000000000 : ℝ)^3299 := by
    have hnat : (4500122693 : ℕ)^4323*100000000000000^3299 ≤ 35122563269429^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500122693 10000000000 35122563269429 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2160578511/5000000000 : ℝ), (1037200751/2500000000 : ℝ), (4500122693/10000000000 : ℝ)] ![(33303613920583/100000000000000 : ℝ), (7893455697709/25000000000000 : ℝ), (35122563269429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2160578511/5000000000 : ℝ)|^4323 ≤ (33303613920583/100000000000000 : ℝ)^3299
        have hw : |(2160578511/5000000000 : ℝ)|=(2160578511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1037200751/2500000000 : ℝ)|^4323 ≤ (7893455697709/25000000000000 : ℝ)^3299
        have hw : |(1037200751/2500000000 : ℝ)|=(1037200751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4500122693/10000000000 : ℝ)|^4323 ≤ (35122563269429/100000000000000 : ℝ)^3299
        have hw : |(4500122693/10000000000 : ℝ)|=(4500122693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s6_4 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1012987841/5000000000 : ℝ)*x 0 + (5245818717/10000000000 : ℝ)*x 1 + (541103457/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1012987841/5000000000 : ℝ)^4323 ≤ (3085712920173/25000000000000 : ℝ)^3299 := by
    have hnat : (1012987841 : ℕ)^4323*25000000000000^3299 ≤ 3085712920173^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012987841 5000000000 3085712920173 25000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245818717/10000000000 : ℝ)^4323 ≤ (42938229731193/100000000000000 : ℝ)^3299 := by
    have hnat : (5245818717 : ℕ)^4323*100000000000000^3299 ≤ 42938229731193^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245818717 10000000000 42938229731193 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541103457/1000000000 : ℝ)^4323 ≤ (11179729641189/25000000000000 : ℝ)^3299 := by
    have hnat : (541103457 : ℕ)^4323*25000000000000^3299 ≤ 11179729641189^3299*1000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541103457 1000000000 11179729641189 25000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1012987841/5000000000 : ℝ), (5245818717/10000000000 : ℝ), (541103457/1000000000 : ℝ)] ![(3085712920173/25000000000000 : ℝ), (42938229731193/100000000000000 : ℝ), (11179729641189/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1012987841/5000000000 : ℝ)|^4323 ≤ (3085712920173/25000000000000 : ℝ)^3299
        have hw : |(-1012987841/5000000000 : ℝ)|=(1012987841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245818717/10000000000 : ℝ)|^4323 ≤ (42938229731193/100000000000000 : ℝ)^3299
        have hw : |(5245818717/10000000000 : ℝ)|=(5245818717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541103457/1000000000 : ℝ)|^4323 ≤ (11179729641189/25000000000000 : ℝ)^3299
        have hw : |(541103457/1000000000 : ℝ)|=(541103457/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s6_5 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652831321/5000000000 : ℝ)*x 0 + (-486230807/2500000000 : ℝ)*x 1 + (676379321/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652831321/5000000000 : ℝ)^4323 ≤ (43581243214361/100000000000000 : ℝ)^3299 := by
    have hnat : (2652831321 : ℕ)^4323*100000000000000^3299 ≤ 43581243214361^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652831321 5000000000 43581243214361 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (486230807/2500000000 : ℝ)^4323 ≤ (467993529163/4000000000000 : ℝ)^3299 := by
    have hnat : (486230807 : ℕ)^4323*4000000000000^3299 ≤ 467993529163^3299*2500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      486230807 2500000000 467993529163 4000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (676379321/1250000000 : ℝ)^4323 ≤ (44718918543097/100000000000000 : ℝ)^3299 := by
    have hnat : (676379321 : ℕ)^4323*100000000000000^3299 ≤ 44718918543097^3299*1250000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676379321 1250000000 44718918543097 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652831321/5000000000 : ℝ), (-486230807/2500000000 : ℝ), (676379321/1250000000 : ℝ)] ![(43581243214361/100000000000000 : ℝ), (467993529163/4000000000000 : ℝ), (44718918543097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652831321/5000000000 : ℝ)|^4323 ≤ (43581243214361/100000000000000 : ℝ)^3299
        have hw : |(2652831321/5000000000 : ℝ)|=(2652831321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-486230807/2500000000 : ℝ)|^4323 ≤ (467993529163/4000000000000 : ℝ)^3299
        have hw : |(-486230807/2500000000 : ℝ)|=(486230807/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(676379321/1250000000 : ℝ)|^4323 ≤ (44718918543097/100000000000000 : ℝ)^3299
        have hw : |(676379321/1250000000 : ℝ)|=(676379321/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s6_6 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66320783/125000000 : ℝ)*x 0 + (541103457/1000000000 : ℝ)*x 1 + (-1944923227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66320783/125000000 : ℝ)^4323 ≤ (21790621596417/50000000000000 : ℝ)^3299 := by
    have hnat : (66320783 : ℕ)^4323*50000000000000^3299 ≤ 21790621596417^3299*125000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66320783 125000000 21790621596417 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541103457/1000000000 : ℝ)^4323 ≤ (11179729641189/25000000000000 : ℝ)^3299 := by
    have hnat : (541103457 : ℕ)^4323*25000000000000^3299 ≤ 11179729641189^3299*1000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541103457 1000000000 11179729641189 25000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1944923227/10000000000 : ℝ)^4323 ≤ (1462479777649/12500000000000 : ℝ)^3299 := by
    have hnat : (1944923227 : ℕ)^4323*12500000000000^3299 ≤ 1462479777649^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1944923227 10000000000 1462479777649 12500000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66320783/125000000 : ℝ), (541103457/1000000000 : ℝ), (-1944923227/10000000000 : ℝ)] ![(21790621596417/50000000000000 : ℝ), (11179729641189/25000000000000 : ℝ), (1462479777649/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66320783/125000000 : ℝ)|^4323 ≤ (21790621596417/50000000000000 : ℝ)^3299
        have hw : |(66320783/125000000 : ℝ)|=(66320783/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541103457/1000000000 : ℝ)|^4323 ≤ (11179729641189/25000000000000 : ℝ)^3299
        have hw : |(541103457/1000000000 : ℝ)|=(541103457/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1944923227/10000000000 : ℝ)|^4323 ≤ (1462479777649/12500000000000 : ℝ)^3299
        have hw : |(-1944923227/10000000000 : ℝ)|=(1944923227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s6_7 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4321182291/10000000000 : ℝ)*x 0 + (2249431239/5000000000 : ℝ)*x 1 + (4150069713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4321182291/10000000000 : ℝ)^4323 ≤ (33303869121767/100000000000000 : ℝ)^3299 := by
    have hnat : (4321182291 : ℕ)^4323*100000000000000^3299 ≤ 33303869121767^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321182291 10000000000 33303869121767 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2249431239/5000000000 : ℝ)^4323 ≤ (35109675120779/100000000000000 : ℝ)^3299 := by
    have hnat : (2249431239 : ℕ)^4323*100000000000000^3299 ≤ 35109675120779^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249431239 5000000000 35109675120779 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4150069713/10000000000 : ℝ)^4323 ≤ (15793227869391/50000000000000 : ℝ)^3299 := by
    have hnat : (4150069713 : ℕ)^4323*50000000000000^3299 ≤ 15793227869391^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4150069713 10000000000 15793227869391 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4321182291/10000000000 : ℝ), (2249431239/5000000000 : ℝ), (4150069713/10000000000 : ℝ)] ![(33303869121767/100000000000000 : ℝ), (35109675120779/100000000000000 : ℝ), (15793227869391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4321182291/10000000000 : ℝ)|^4323 ≤ (33303869121767/100000000000000 : ℝ)^3299
        have hw : |(4321182291/10000000000 : ℝ)|=(4321182291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2249431239/5000000000 : ℝ)|^4323 ≤ (35109675120779/100000000000000 : ℝ)^3299
        have hw : |(2249431239/5000000000 : ℝ)|=(2249431239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4150069713/10000000000 : ℝ)|^4323 ≤ (15793227869391/50000000000000 : ℝ)^3299
        have hw : |(4150069713/10000000000 : ℝ)|=(4150069713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1363_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155556687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14727/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11191/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11197/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14721/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14727/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11191/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14727/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11191/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14727/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11191/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14727/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11191/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14727/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11191/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14727/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11191/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11191/100000 : ℝ) ^ (2161/512 : ℝ) ≤ (4836464231978259/50000000000000000000 : ℝ) := by
    have hpowers : (11191/100000 : ℝ)^2161 ≤ (4836464231978259/50000000000000000000 : ℝ)^512 := by
      have hnat : (11191 : ℕ)^2161*50000000000000000000^512 ≤ 4836464231978259^512*100000^2161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11191 100000 4836464231978259 50000000000000000000 2161 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11191/100000 : ℝ)) (X := (4836464231978259/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14727/100000 : ℝ) ^ (2161/512 : ℝ) ≤ (3852719435248497/12500000000000000000 : ℝ) := by
    have hpowers : (14727/100000 : ℝ)^2161 ≤ (3852719435248497/12500000000000000000 : ℝ)^512 := by
      have hnat : (14727 : ℕ)^2161*12500000000000000000^512 ≤ 3852719435248497^512*100000^2161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14727 100000 3852719435248497 12500000000000000000 2161 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14727/100000 : ℝ)) (X := (3852719435248497/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004836464231978259/25000000000000000000 : ℝ) ≤ (5000229161215219/5000000000000000 : ℝ) ^ (2161/512 : ℝ) := by
    have hpowers : (25004836464231978259/25000000000000000000 : ℝ)^512 ≤ (5000229161215219/5000000000000000 : ℝ)^2161 := by
      have hnat : (25004836464231978259 : ℕ)^512*5000000000000000^2161 ≤ 5000229161215219^2161*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004836464231978259 25000000000000000000 5000229161215219 5000000000000000 512 2161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000229161215219/5000000000000000 : ℝ)) (X := (25004836464231978259/25000000000000000000 : ℝ)) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020247341972972247/50000000000000000000 : ℝ) ≤ (5000479640805437/5000000000000000 : ℝ) ^ (2161/512 : ℝ) := by
    have hpowers : (50020247341972972247/50000000000000000000 : ℝ)^512 ≤ (5000479640805437/5000000000000000 : ℝ)^2161 := by
      have hnat : (50020247341972972247 : ℕ)^512*5000000000000000^2161 ≤ 5000479640805437^2161*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020247341972972247 50000000000000000000 5000479640805437 5000000000000000 512 2161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000479640805437/5000000000000000 : ℝ)) (X := (50020247341972972247/50000000000000000000 : ℝ)) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (6253852719435248497/6250000000000000000 : ℝ) ≤ (1000146024079131/1000000000000000 : ℝ) ^ (2161/512 : ℝ) := by
    have hpowers : (6253852719435248497/6250000000000000000 : ℝ)^512 ≤ (1000146024079131/1000000000000000 : ℝ)^2161 := by
      have hnat : (6253852719435248497 : ℕ)^512*1000000000000000^2161 ≤ 1000146024079131^2161*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253852719435248497 6250000000000000000 1000146024079131 1000000000000000 512 2161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000146024079131/1000000000000000 : ℝ)) (X := (6253852719435248497/6250000000000000000 : ℝ)) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4836464231978259/50000000000000000000 : ℝ) ≤ ((339907770766706829/340000000000000000 : ℝ)+2*(9633830393/6800000000000 : ℝ)*(11191/100000 : ℝ))^(2161/512 : ℝ) := by
    rw [show (339907770766706829/340000000000000000 : ℝ)+2*(9633830393/6800000000000 : ℝ)*(11191/100000 : ℝ)=(5000229161215219/5000000000000000 : ℝ) by norm_num, show 1+2*(4836464231978259/50000000000000000000 : ℝ)=(25004836464231978259/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3852719435248497/12500000000000000000 : ℝ)+(4836464231978259/50000000000000000000 : ℝ) ≤ ((339907770766706829/340000000000000000 : ℝ)+(9633830393/6800000000000 : ℝ)*((14727/100000 : ℝ)+(11191/100000 : ℝ)))^(2161/512 : ℝ) := by
    rw [show (339907770766706829/340000000000000000 : ℝ)+(9633830393/6800000000000 : ℝ)*((14727/100000 : ℝ)+(11191/100000 : ℝ))=(5000479640805437/5000000000000000 : ℝ) by norm_num, show 1+(3852719435248497/12500000000000000000 : ℝ)+(4836464231978259/50000000000000000000 : ℝ)=(50020247341972972247/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3852719435248497/12500000000000000000 : ℝ) ≤ ((339907770766706829/340000000000000000 : ℝ)+2*(9633830393/6800000000000 : ℝ)*(14727/100000 : ℝ))^(2161/512 : ℝ) := by
    rw [show (339907770766706829/340000000000000000 : ℝ)+2*(9633830393/6800000000000 : ℝ)*(14727/100000 : ℝ)=(1000146024079131/1000000000000000 : ℝ) by norm_num, show 1+2*(3852719435248497/12500000000000000000 : ℝ)=(6253852719435248497/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (339907770766706829/340000000000000000 : ℝ)*(X 1 0+X 2 0)+(9633830393/6800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2161/512 : ℝ)) (lo := (11191/100000 : ℝ)) (hi := (14727/100000 : ℝ)) (c := (339907770766706829/340000000000000000 : ℝ)) (alpha := (9633830393/6800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (339907770766706829/340000000000000000 : ℝ)*(X 0 1+X 2 1)+(9633830393/6800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2161/512 : ℝ)) (lo := (11191/100000 : ℝ)) (hi := (14727/100000 : ℝ)) (c := (339907770766706829/340000000000000000 : ℝ)) (alpha := (9633830393/6800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (339907770766706829/340000000000000000 : ℝ)*(X 0 2+X 1 2)+(9633830393/6800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2161/512 : ℝ)) (lo := (11191/100000 : ℝ)) (hi := (14727/100000 : ℝ)) (c := (339907770766706829/340000000000000000 : ℝ)) (alpha := (9633830393/6800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-506490933/2500000000 : ℝ)*X 0 0+(5411634547/10000000000 : ℝ)*X 0 1+(1311305453/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334289297/625000000 : ℝ)*X 1 0+(-65960501/312500000 : ℝ)*X 1 1+(5245221771/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069725753/2000000000 : ℝ)*X 2 0+(5245221787/10000000000 : ℝ)*X 2 1+(-2110735993/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2160578511/5000000000 : ℝ)*X 0 0+(1037200751/2500000000 : ℝ)*X 0 1+(4500122693/10000000000 : ℝ)*X 0 2+(2160578511/5000000000 : ℝ)*X 1 0+(1037200751/2500000000 : ℝ)*X 1 1+(4500122693/10000000000 : ℝ)*X 1 2+(2160578511/5000000000 : ℝ)*X 2 0+(1037200751/2500000000 : ℝ)*X 2 1+(4500122693/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1012987841/5000000000 : ℝ)*X 0 0+(5245818717/10000000000 : ℝ)*X 0 1+(541103457/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652831321/5000000000 : ℝ)*X 1 0+(-486230807/2500000000 : ℝ)*X 1 1+(676379321/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((66320783/125000000 : ℝ)*X 2 0+(541103457/1000000000 : ℝ)*X 2 1+(-1944923227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4321182291/10000000000 : ℝ)*X 0 0+(2249431239/5000000000 : ℝ)*X 0 1+(4150069713/10000000000 : ℝ)*X 0 2+(4321182291/10000000000 : ℝ)*X 1 0+(2249431239/5000000000 : ℝ)*X 1 1+(4150069713/10000000000 : ℝ)*X 1 2+(4321182291/10000000000 : ℝ)*X 2 0+(2249431239/5000000000 : ℝ)*X 2 1+(4150069713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3534161071432986175554909/425000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (311689411/20000000000000 : ℝ)*(base19) + (1487977951/100000000000000 : ℝ)*(base23) + (45503291/100000000000000 : ℝ)*(lower2) + (178283369/100000000000000 : ℝ)*(upper3) + (10392349/6250000000000 : ℝ)*(upper5) + (221391542760493/5000000000000 : ℝ)*(major0) + (221391542760493/5000000000000 : ℝ)*(major1) + (221391542760493/5000000000000 : ℝ)*(major2) + (3004593496490471/50000000000000 : ℝ)*(sp0) + (3004608942973879/50000000000000 : ℝ)*(sp1) + (3004608978208431/50000000000000 : ℝ)*(sp2) + (711606455019031/25000000000000 : ℝ)*(sp3) + (2028213367/6250000000000 : ℝ)*(sp4) + (16168759663/100000000000000 : ℝ)*(sp7) + (1423220994417893/50000000000000 : ℝ)*(f.failure) + (3004609722197407/50000000000000 : ℝ)*(f.sum) + (2752052341/2125000000000000000000000 : ℝ)*base65 + (25656728938356697/1700000000000000000000000000000 : ℝ)*base67 + (24754736670456697/1700000000000000000000000000000 : ℝ)*base69 + (9942843931056697/1700000000000000000000000000000 : ℝ)*base71 + (52971783869/17000000000000000000000000 : ℝ)*base74 + (23765374964656697/1700000000000000000000000000000 : ℝ)*base75 + (11276498327256697/1700000000000000000000000000000 : ℝ)*base77 + (1417006784843303/1700000000000000000000000000000 : ℝ)*base80 + (1747720737/2125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (71399509/5000000000000000000000 : ℝ)*base90 + (71399509/5000000000000000000000 : ℝ)*base92 + (71399509/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (99831405325496731745886399/8500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2028817207/100000000000000 : ℝ)*(base19) + (2203815021/100000000000000 : ℝ)*(base23) + (239311699/100000000000000 : ℝ)*(upper3) + (40161857/50000000000000 : ℝ)*(lower4) + (240672127/100000000000000 : ℝ)*(upper5) + (2229929515864777/50000000000000 : ℝ)*(major0) + (2229929515864777/50000000000000 : ℝ)*(major1) + (2229929515864777/50000000000000 : ℝ)*(major2) + (41643044409/100000000000000 : ℝ)*(sp1) + (44839678151/100000000000000 : ℝ)*(sp2) + (1210537258167529/20000000000000 : ℝ)*(sp4) + (605264261897603/10000000000000 : ℝ)*(sp5) + (756579905918059/12500000000000 : ℝ)*(sp6) + (1433515690562873/50000000000000 : ℝ)*(sp7) + (1433515690562873/50000000000000 : ℝ)*(f.failure) + (1210537258167529/20000000000000 : ℝ)*(f.sum) + (160874184041/170000000000000000000000000 : ℝ)*base65 + (110748495833512133/17000000000000000000000000000000 : ℝ)*base67 + (158955798581487867/17000000000000000000000000000000 : ℝ)*base70 + (297302892803487867/17000000000000000000000000000000 : ℝ)*base72 + (428577695161/170000000000000000000000000 : ℝ)*base73 + (236265775974487867/17000000000000000000000000000000 : ℝ)*base76 + (69958845842487867/17000000000000000000000000000000 : ℝ)*base78 + (201965881829512133/17000000000000000000000000000000 : ℝ)*base79 + (132490670509/170000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (10918249/5000000000000000000000 : ℝ)*base90 + (10918249/5000000000000000000000 : ℝ)*base92 + (10918249/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1363_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155556687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14727/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11191/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11197/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14721/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1363_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1363_s7_0 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-126623023/625000000 : ℝ)*x 0 + (5411586563/10000000000 : ℝ)*x 1 + (1311316703/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (126623023/625000000 : ℝ)^4323 ≤ (12342793290633/100000000000000 : ℝ)^3299 := by
    have hnat : (126623023 : ℕ)^4323*100000000000000^3299 ≤ 12342793290633^3299*625000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126623023 625000000 12342793290633 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5411586563/10000000000 : ℝ)^4323 ≤ (5590612067909/12500000000000 : ℝ)^3299 := by
    have hnat : (5411586563 : ℕ)^4323*12500000000000^3299 ≤ 5590612067909^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411586563 10000000000 5590612067909 12500000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311316703/2500000000 : ℝ)^4323 ≤ (1073307753739/2500000000000 : ℝ)^3299 := by
    have hnat : (1311316703 : ℕ)^4323*2500000000000^3299 ≤ 1073307753739^3299*2500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311316703 2500000000 1073307753739 2500000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-126623023/625000000 : ℝ), (5411586563/10000000000 : ℝ), (1311316703/2500000000 : ℝ)] ![(12342793290633/100000000000000 : ℝ), (5590612067909/12500000000000 : ℝ), (1073307753739/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-126623023/625000000 : ℝ)|^4323 ≤ (12342793290633/100000000000000 : ℝ)^3299
        have hw : |(-126623023/625000000 : ℝ)|=(126623023/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5411586563/10000000000 : ℝ)|^4323 ≤ (5590612067909/12500000000000 : ℝ)^3299
        have hw : |(5411586563/10000000000 : ℝ)|=(5411586563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311316703/2500000000 : ℝ)|^4323 ≤ (1073307753739/2500000000000 : ℝ)^3299
        have hw : |(1311316703/2500000000 : ℝ)|=(1311316703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s7_1 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674308347/5000000000 : ℝ)*x 0 + (-211069239/1000000000 : ℝ)*x 1 + (5245266801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674308347/5000000000 : ℝ)^4323 ≤ (44044168993381/100000000000000 : ℝ)^3299 := by
    have hnat : (2674308347 : ℕ)^4323*100000000000000^3299 ≤ 44044168993381^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674308347 5000000000 44044168993381 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211069239/1000000000 : ℝ)^4323 ≤ (13023520948409/100000000000000 : ℝ)^3299 := by
    have hnat : (211069239 : ℕ)^4323*100000000000000^3299 ≤ 13023520948409^3299*1000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211069239 1000000000 13023520948409 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245266801/10000000000 : ℝ)^4323 ≤ (42932310031579/100000000000000 : ℝ)^3299 := by
    have hnat : (5245266801 : ℕ)^4323*100000000000000^3299 ≤ 42932310031579^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245266801 10000000000 42932310031579 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674308347/5000000000 : ℝ), (-211069239/1000000000 : ℝ), (5245266801/10000000000 : ℝ)] ![(44044168993381/100000000000000 : ℝ), (13023520948409/100000000000000 : ℝ), (42932310031579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674308347/5000000000 : ℝ)|^4323 ≤ (44044168993381/100000000000000 : ℝ)^3299
        have hw : |(2674308347/5000000000 : ℝ)|=(2674308347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-211069239/1000000000 : ℝ)|^4323 ≤ (13023520948409/100000000000000 : ℝ)^3299
        have hw : |(-211069239/1000000000 : ℝ)|=(211069239/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245266801/10000000000 : ℝ)|^4323 ≤ (42932310031579/100000000000000 : ℝ)^3299
        have hw : |(5245266801/10000000000 : ℝ)|=(5245266801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s7_2 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348616687/10000000000 : ℝ)*x 0 + (40978647/78125000 : ℝ)*x 1 + (-2110692381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348616687/10000000000 : ℝ)^4323 ≤ (22022084458923/50000000000000 : ℝ)^3299 := by
    have hnat : (5348616687 : ℕ)^4323*50000000000000^3299 ≤ 22022084458923^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348616687 10000000000 22022084458923 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40978647/78125000 : ℝ)^4323 ≤ (21466155096231/50000000000000 : ℝ)^3299 := by
    have hnat : (40978647 : ℕ)^4323*50000000000000^3299 ≤ 21466155096231^3299*78125000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40978647 78125000 21466155096231 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2110692381/10000000000 : ℝ)^4323 ≤ (13023520875639/100000000000000 : ℝ)^3299 := by
    have hnat : (2110692381 : ℕ)^4323*100000000000000^3299 ≤ 13023520875639^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110692381 10000000000 13023520875639 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348616687/10000000000 : ℝ), (40978647/78125000 : ℝ), (-2110692381/10000000000 : ℝ)] ![(22022084458923/50000000000000 : ℝ), (21466155096231/50000000000000 : ℝ), (13023520875639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348616687/10000000000 : ℝ)|^4323 ≤ (22022084458923/50000000000000 : ℝ)^3299
        have hw : |(5348616687/10000000000 : ℝ)|=(5348616687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40978647/78125000 : ℝ)|^4323 ≤ (21466155096231/50000000000000 : ℝ)^3299
        have hw : |(40978647/78125000 : ℝ)|=(40978647/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2110692381/10000000000 : ℝ)|^4323 ≤ (13023520875639/100000000000000 : ℝ)^3299
        have hw : |(-2110692381/10000000000 : ℝ)|=(2110692381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s7_3 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2160580159/5000000000 : ℝ)*x 0 + (414890083/1000000000 : ℝ)*x 1 + (90000481/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160580159/5000000000 : ℝ)^4323 ≤ (33303647208107/100000000000000 : ℝ)^3299 := by
    have hnat : (2160580159 : ℕ)^4323*100000000000000^3299 ≤ 33303647208107^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160580159 5000000000 33303647208107 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (414890083/1000000000 : ℝ)^4323 ≤ (31574798371443/100000000000000 : ℝ)^3299 := by
    have hnat : (414890083 : ℕ)^4323*100000000000000^3299 ≤ 31574798371443^3299*1000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414890083 1000000000 31574798371443 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90000481/200000000 : ℝ)^4323 ≤ (17560777206271/50000000000000 : ℝ)^3299 := by
    have hnat : (90000481 : ℕ)^4323*50000000000000^3299 ≤ 17560777206271^3299*200000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90000481 200000000 17560777206271 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2160580159/5000000000 : ℝ), (414890083/1000000000 : ℝ), (90000481/200000000 : ℝ)] ![(33303647208107/100000000000000 : ℝ), (31574798371443/100000000000000 : ℝ), (17560777206271/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2160580159/5000000000 : ℝ)|^4323 ≤ (33303647208107/100000000000000 : ℝ)^3299
        have hw : |(2160580159/5000000000 : ℝ)|=(2160580159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(414890083/1000000000 : ℝ)|^4323 ≤ (31574798371443/100000000000000 : ℝ)^3299
        have hw : |(414890083/1000000000 : ℝ)|=(414890083/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(90000481/200000000 : ℝ)|^4323 ≤ (17560777206271/50000000000000 : ℝ)^3299
        have hw : |(90000481/200000000 : ℝ)|=(90000481/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s7_4 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-63311879/312500000 : ℝ)*x 0 + (2622931559/5000000000 : ℝ)*x 1 + (2705493659/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (63311879/312500000 : ℝ)^4323 ≤ (61714435873/500000000000 : ℝ)^3299 := by
    have hnat : (63311879 : ℕ)^4323*500000000000^3299 ≤ 61714435873^3299*312500000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63311879 312500000 61714435873 500000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622931559/5000000000 : ℝ)^4323 ≤ (42938705972541/100000000000000 : ℝ)^3299 := by
    have hnat : (2622931559 : ℕ)^4323*100000000000000^3299 ≤ 42938705972541^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622931559 5000000000 42938705972541 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705493659/5000000000 : ℝ)^4323 ≤ (44718406843437/100000000000000 : ℝ)^3299 := by
    have hnat : (2705493659 : ℕ)^4323*100000000000000^3299 ≤ 44718406843437^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705493659 5000000000 44718406843437 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-63311879/312500000 : ℝ), (2622931559/5000000000 : ℝ), (2705493659/5000000000 : ℝ)] ![(61714435873/500000000000 : ℝ), (42938705972541/100000000000000 : ℝ), (44718406843437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-63311879/312500000 : ℝ)|^4323 ≤ (61714435873/500000000000 : ℝ)^3299
        have hw : |(-63311879/312500000 : ℝ)|=(63311879/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622931559/5000000000 : ℝ)|^4323 ≤ (42938705972541/100000000000000 : ℝ)^3299
        have hw : |(2622931559/5000000000 : ℝ)|=(2622931559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705493659/5000000000 : ℝ)|^4323 ≤ (44718406843437/100000000000000 : ℝ)^3299
        have hw : |(2705493659/5000000000 : ℝ)|=(2705493659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s7_5 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265283729/500000000 : ℝ)*x 0 + (-388994323/2000000000 : ℝ)*x 1 + (2705493741/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265283729/500000000 : ℝ)^4323 ≤ (43581371711847/100000000000000 : ℝ)^3299 := by
    have hnat : (265283729 : ℕ)^4323*100000000000000^3299 ≤ 43581371711847^3299*500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265283729 500000000 43581371711847 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (388994323/2000000000 : ℝ)^4323 ≤ (11700219655421/100000000000000 : ℝ)^3299 := by
    have hnat : (388994323 : ℕ)^4323*100000000000000^3299 ≤ 11700219655421^3299*2000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388994323 2000000000 11700219655421 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705493741/5000000000 : ℝ)^4323 ≤ (44718408619493/100000000000000 : ℝ)^3299 := by
    have hnat : (2705493741 : ℕ)^4323*100000000000000^3299 ≤ 44718408619493^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705493741 5000000000 44718408619493 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265283729/500000000 : ℝ), (-388994323/2000000000 : ℝ), (2705493741/5000000000 : ℝ)] ![(43581371711847/100000000000000 : ℝ), (11700219655421/100000000000000 : ℝ), (44718408619493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265283729/500000000 : ℝ)|^4323 ≤ (43581371711847/100000000000000 : ℝ)^3299
        have hw : |(265283729/500000000 : ℝ)|=(265283729/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-388994323/2000000000 : ℝ)|^4323 ≤ (11700219655421/100000000000000 : ℝ)^3299
        have hw : |(-388994323/2000000000 : ℝ)|=(388994323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705493741/5000000000 : ℝ)|^4323 ≤ (44718408619493/100000000000000 : ℝ)^3299
        have hw : |(2705493741/5000000000 : ℝ)|=(2705493741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s7_6 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305674549/10000000000 : ℝ)*x 0 + (1352746829/2500000000 : ℝ)*x 1 + (-388994377/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305674549/10000000000 : ℝ)^4323 ≤ (43581371378171/100000000000000 : ℝ)^3299 := by
    have hnat : (5305674549 : ℕ)^4323*100000000000000^3299 ≤ 43581371378171^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305674549 10000000000 43581371378171 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352746829/2500000000 : ℝ)^4323 ≤ (22359203410889/50000000000000 : ℝ)^3299 := by
    have hnat : (1352746829 : ℕ)^4323*50000000000000^3299 ≤ 22359203410889^3299*2500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352746829 2500000000 22359203410889 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (388994377/2000000000 : ℝ)^4323 ≤ (731263861487/6250000000000 : ℝ)^3299 := by
    have hnat : (388994377 : ℕ)^4323*6250000000000^3299 ≤ 731263861487^3299*2000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388994377 2000000000 731263861487 6250000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305674549/10000000000 : ℝ), (1352746829/2500000000 : ℝ), (-388994377/2000000000 : ℝ)] ![(43581371378171/100000000000000 : ℝ), (22359203410889/50000000000000 : ℝ), (731263861487/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305674549/10000000000 : ℝ)|^4323 ≤ (43581371378171/100000000000000 : ℝ)^3299
        have hw : |(5305674549/10000000000 : ℝ)|=(5305674549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352746829/2500000000 : ℝ)|^4323 ≤ (22359203410889/50000000000000 : ℝ)^3299
        have hw : |(1352746829/2500000000 : ℝ)|=(1352746829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-388994377/2000000000 : ℝ)|^4323 ≤ (731263861487/6250000000000 : ℝ)^3299
        have hw : |(-388994377/2000000000 : ℝ)|=(388994377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s7_7 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4321185551/10000000000 : ℝ)*x 0 + (4498765127/10000000000 : ℝ)*x 1 + (518770779/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4321185551/10000000000 : ℝ)^4323 ≤ (16651951022887/50000000000000 : ℝ)^3299 := by
    have hnat : (4321185551 : ℕ)^4323*50000000000000^3299 ≤ 16651951022887^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321185551 10000000000 16651951022887 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4498765127/10000000000 : ℝ)^4323 ≤ (35108679564143/100000000000000 : ℝ)^3299 := by
    have hnat : (4498765127 : ℕ)^4323*100000000000000^3299 ≤ 35108679564143^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498765127 10000000000 35108679564143 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518770779/1250000000 : ℝ)^4323 ≤ (631748367527/2000000000000 : ℝ)^3299 := by
    have hnat : (518770779 : ℕ)^4323*2000000000000^3299 ≤ 631748367527^3299*1250000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518770779 1250000000 631748367527 2000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4321185551/10000000000 : ℝ), (4498765127/10000000000 : ℝ), (518770779/1250000000 : ℝ)] ![(16651951022887/50000000000000 : ℝ), (35108679564143/100000000000000 : ℝ), (631748367527/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4321185551/10000000000 : ℝ)|^4323 ≤ (16651951022887/50000000000000 : ℝ)^3299
        have hw : |(4321185551/10000000000 : ℝ)|=(4321185551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4498765127/10000000000 : ℝ)|^4323 ≤ (35108679564143/100000000000000 : ℝ)^3299
        have hw : |(4498765127/10000000000 : ℝ)|=(4498765127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518770779/1250000000 : ℝ)|^4323 ≤ (631748367527/2000000000000 : ℝ)^3299
        have hw : |(518770779/1250000000 : ℝ)|=(518770779/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1363_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155556687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14721/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11197/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5599/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (92/625 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14721/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11197/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14721/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11197/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14721/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11197/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14721/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11197/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14721/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11197/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14721/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11197/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11197/100000 : ℝ) ^ (2161/512 : ℝ) ≤ (9694836330443347/100000000000000000000 : ℝ) := by
    have hpowers : (11197/100000 : ℝ)^2161 ≤ (9694836330443347/100000000000000000000 : ℝ)^512 := by
      have hnat : (11197 : ℕ)^2161*100000000000000000000^512 ≤ 9694836330443347^512*100000^2161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11197 100000 9694836330443347 100000000000000000000 2161 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11197/100000 : ℝ)) (X := (9694836330443347/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14721/100000 : ℝ) ^ (2161/512 : ℝ) ≤ (6153757968987377/20000000000000000000 : ℝ) := by
    have hpowers : (14721/100000 : ℝ)^2161 ≤ (6153757968987377/20000000000000000000 : ℝ)^512 := by
      have hnat : (14721 : ℕ)^2161*20000000000000000000^512 ≤ 6153757968987377^512*100000^2161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14721 100000 6153757968987377 20000000000000000000 2161 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14721/100000 : ℝ)) (X := (6153757968987377/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009694836330443347/50000000000000000000 : ℝ) ≤ (2000091872078317/2000000000000000 : ℝ) ^ (2161/512 : ℝ) := by
    have hpowers : (50009694836330443347/50000000000000000000 : ℝ)^512 ≤ (2000091872078317/2000000000000000 : ℝ)^2161 := by
      have hnat : (50009694836330443347 : ℕ)^512*2000000000000000^2161 ≤ 2000091872078317^2161*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009694836330443347 50000000000000000000 2000091872078317 2000000000000000 512 2161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000091872078317/2000000000000000 : ℝ)) (X := (50009694836330443347/50000000000000000000 : ℝ)) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505057953271922529/12500000000000000000 : ℝ) ≤ (10000958545994561/10000000000000000 : ℝ) ^ (2161/512 : ℝ) := by
    have hpowers : (12505057953271922529/12500000000000000000 : ℝ)^512 ≤ (10000958545994561/10000000000000000 : ℝ)^2161 := by
      have hnat : (12505057953271922529 : ℕ)^512*10000000000000000^2161 ≤ 10000958545994561^2161*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505057953271922529 12500000000000000000 10000958545994561 10000000000000000 512 2161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000958545994561/10000000000000000 : ℝ)) (X := (12505057953271922529/12500000000000000000 : ℝ)) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006153757968987377/10000000000000000000 : ℝ) ≤ (10001457731597537/10000000000000000 : ℝ) ^ (2161/512 : ℝ) := by
    have hpowers : (10006153757968987377/10000000000000000000 : ℝ)^512 ≤ (10001457731597537/10000000000000000 : ℝ)^2161 := by
      have hnat : (10006153757968987377 : ℕ)^512*10000000000000000^2161 ≤ 10001457731597537^2161*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006153757968987377 10000000000000000000 10001457731597537 10000000000000000 512 2161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001457731597537/10000000000000000 : ℝ)) (X := (10006153757968987377/10000000000000000000 : ℝ)) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9694836330443347/100000000000000000000 : ℝ) ≤ ((8807610005906725249/8810000000000000000 : ℝ)+2*(15599550093/11012500000000 : ℝ)*(11197/100000 : ℝ))^(2161/512 : ℝ) := by
    rw [show (8807610005906725249/8810000000000000000 : ℝ)+2*(15599550093/11012500000000 : ℝ)*(11197/100000 : ℝ)=(2000091872078317/2000000000000000 : ℝ) by norm_num, show 1+2*(9694836330443347/100000000000000000000 : ℝ)=(50009694836330443347/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6153757968987377/20000000000000000000 : ℝ)+(9694836330443347/100000000000000000000 : ℝ) ≤ ((8807610005906725249/8810000000000000000 : ℝ)+(15599550093/11012500000000 : ℝ)*((14721/100000 : ℝ)+(11197/100000 : ℝ)))^(2161/512 : ℝ) := by
    rw [show (8807610005906725249/8810000000000000000 : ℝ)+(15599550093/11012500000000 : ℝ)*((14721/100000 : ℝ)+(11197/100000 : ℝ))=(10000958545994561/10000000000000000 : ℝ) by norm_num, show 1+(6153757968987377/20000000000000000000 : ℝ)+(9694836330443347/100000000000000000000 : ℝ)=(12505057953271922529/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6153757968987377/20000000000000000000 : ℝ) ≤ ((8807610005906725249/8810000000000000000 : ℝ)+2*(15599550093/11012500000000 : ℝ)*(14721/100000 : ℝ))^(2161/512 : ℝ) := by
    rw [show (8807610005906725249/8810000000000000000 : ℝ)+2*(15599550093/11012500000000 : ℝ)*(14721/100000 : ℝ)=(10001457731597537/10000000000000000 : ℝ) by norm_num, show 1+2*(6153757968987377/20000000000000000000 : ℝ)=(10006153757968987377/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8807610005906725249/8810000000000000000 : ℝ)*(X 1 0+X 2 0)+(15599550093/11012500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2161/512 : ℝ)) (lo := (11197/100000 : ℝ)) (hi := (14721/100000 : ℝ)) (c := (8807610005906725249/8810000000000000000 : ℝ)) (alpha := (15599550093/11012500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8807610005906725249/8810000000000000000 : ℝ)*(X 0 1+X 2 1)+(15599550093/11012500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2161/512 : ℝ)) (lo := (11197/100000 : ℝ)) (hi := (14721/100000 : ℝ)) (c := (8807610005906725249/8810000000000000000 : ℝ)) (alpha := (15599550093/11012500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8807610005906725249/8810000000000000000 : ℝ)*(X 0 2+X 1 2)+(15599550093/11012500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2161/512 : ℝ)) (lo := (11197/100000 : ℝ)) (hi := (14721/100000 : ℝ)) (c := (8807610005906725249/8810000000000000000 : ℝ)) (alpha := (15599550093/11012500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-126623023/625000000 : ℝ)*X 0 0+(5411586563/10000000000 : ℝ)*X 0 1+(1311316703/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674308347/5000000000 : ℝ)*X 1 0+(-211069239/1000000000 : ℝ)*X 1 1+(5245266801/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348616687/10000000000 : ℝ)*X 2 0+(40978647/78125000 : ℝ)*X 2 1+(-2110692381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2160580159/5000000000 : ℝ)*X 0 0+(414890083/1000000000 : ℝ)*X 0 1+(90000481/200000000 : ℝ)*X 0 2+(2160580159/5000000000 : ℝ)*X 1 0+(414890083/1000000000 : ℝ)*X 1 1+(90000481/200000000 : ℝ)*X 1 2+(2160580159/5000000000 : ℝ)*X 2 0+(414890083/1000000000 : ℝ)*X 2 1+(90000481/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-63311879/312500000 : ℝ)*X 0 0+(2622931559/5000000000 : ℝ)*X 0 1+(2705493659/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265283729/500000000 : ℝ)*X 1 0+(-388994323/2000000000 : ℝ)*X 1 1+(2705493741/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305674549/10000000000 : ℝ)*X 2 0+(1352746829/2500000000 : ℝ)*X 2 1+(-388994377/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4321185551/10000000000 : ℝ)*X 0 0+(4498765127/10000000000 : ℝ)*X 0 1+(518770779/1250000000 : ℝ)*X 0 2+(4321185551/10000000000 : ℝ)*X 1 0+(4498765127/10000000000 : ℝ)*X 1 1+(518770779/1250000000 : ℝ)*X 1 2+(4321185551/10000000000 : ℝ)*X 2 0+(4498765127/10000000000 : ℝ)*X 2 1+(518770779/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (872521947449982492193117317/110125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (93112711/6250000000000 : ℝ)*(base19) + (1403550733/100000000000000 : ℝ)*(base23) + (4192443/10000000000000 : ℝ)*(lower2) + (191437029/100000000000000 : ℝ)*(upper3) + (72212347/50000000000000 : ℝ)*(upper5) + (1107576258405311/25000000000000 : ℝ)*(major0) + (1107576258405311/25000000000000 : ℝ)*(major1) + (1107576258405311/25000000000000 : ℝ)*(major2) + (1503136622285907/25000000000000 : ℝ)*(sp0) + (240503031712289/4000000000000 : ℝ)*(sp1) + (1503143969764967/25000000000000 : ℝ)*(sp2) + (1424008620477557/50000000000000 : ℝ)*(sp3) + (30793466973/100000000000000 : ℝ)*(sp4) + (15279576289/100000000000000 : ℝ)*(sp7) + (1424016260265701/50000000000000 : ℝ)*(f.failure) + (3006288641305301/50000000000000 : ℝ)*(f.sum) + (23262230977879/4405000000000000000000000000 : ℝ)*base66 + (204944557797452561/220250000000000000000000000000000 : ℝ)*base68 + (697442510763297439/220250000000000000000000000000000 : ℝ)*base69 + (1287118692082452561/220250000000000000000000000000000 : ℝ)*base72 + (10074567218529/4405000000000000000000000000 : ℝ)*base74 + (69228990455452561/220250000000000000000000000000000 : ℝ)*base76 + (207453889393952561/220250000000000000000000000000000 : ℝ)*base78 + (1287454485025047439/220250000000000000000000000000000 : ℝ)*base79 + (106362644263/34414062500000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (12707413/5000000000000000000000 : ℝ)*base90 + (12707413/5000000000000000000000 : ℝ)*base92 + (12707413/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1063894243917908371361453991/88100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (476238297/25000000000000 : ℝ)*(base19) + (434344143/20000000000000 : ℝ)*(base23) + (727176749/100000000000000 : ℝ)*(lower1) + (72883237/50000000000000 : ℝ)*(upper3) + (37273877/20000000000000 : ℝ)*(lower4) + (62977279/25000000000000 : ℝ)*(upper5) + (892460508243249/20000000000000 : ℝ)*(major0) + (892460508243249/20000000000000 : ℝ)*(major1) + (892460508243249/20000000000000 : ℝ)*(major2) + (1517019797/25000000000000 : ℝ)*(sp1) + (6056002482672201/100000000000000 : ℝ)*(sp4) + (242239780385593/4000000000000 : ℝ)*(sp5) + (1211200062190297/20000000000000 : ℝ)*(sp6) + (1434301098613731/50000000000000 : ℝ)*(sp7) + (1434301098613731/50000000000000 : ℝ)*(f.failure) + (6056002482672201/100000000000000 : ℝ)*(f.sum) + (1629129771751/440500000000000000000000000 : ℝ)*base65 + (278876820157294001/176200000000000000000000000000000 : ℝ)*base67 + (1541911949255294001/176200000000000000000000000000000 : ℝ)*base69 + (674919068336894001/176200000000000000000000000000000 : ℝ)*base71 + (3009166655243/881000000000000000000000000 : ℝ)*base74 + (3709707364671294001/176200000000000000000000000000000 : ℝ)*base75 + (669748956310294001/176200000000000000000000000000000 : ℝ)*base77 + (645975152456894001/176200000000000000000000000000000 : ℝ)*base79 + (262256829377/881000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (37069197/5000000000000000000000 : ℝ)*base89 + (37069197/5000000000000000000000 : ℝ)*base91 + (37069197/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1363_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155556687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14721/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11197/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5599/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (92/625 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1363_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1363_s8_0 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348614749/10000000000 : ℝ)*x 0 + (-527671287/2500000000 : ℝ)*x 1 + (2622637109/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348614749/10000000000 : ℝ)^4323 ≤ (22022074002729/50000000000000 : ℝ)^3299 := by
    have hnat : (5348614749 : ℕ)^4323*50000000000000^3299 ≤ 22022074002729^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348614749 10000000000 22022074002729 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (527671287/2500000000 : ℝ)^4323 ≤ (2604692478663/20000000000000 : ℝ)^3299 := by
    have hnat : (527671287 : ℕ)^4323*20000000000000^3299 ≤ 2604692478663^3299*2500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527671287 2500000000 2604692478663 20000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622637109/5000000000 : ℝ)^4323 ≤ (10733097395751/25000000000000 : ℝ)^3299 := by
    have hnat : (2622637109 : ℕ)^4323*25000000000000^3299 ≤ 10733097395751^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622637109 5000000000 10733097395751 25000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348614749/10000000000 : ℝ), (-527671287/2500000000 : ℝ), (2622637109/5000000000 : ℝ)] ![(22022074002729/50000000000000 : ℝ), (2604692478663/20000000000000 : ℝ), (10733097395751/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348614749/10000000000 : ℝ)|^4323 ≤ (22022074002729/50000000000000 : ℝ)^3299
        have hw : |(5348614749/10000000000 : ℝ)|=(5348614749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-527671287/2500000000 : ℝ)|^4323 ≤ (2604692478663/20000000000000 : ℝ)^3299
        have hw : |(-527671287/2500000000 : ℝ)|=(527671287/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622637109/5000000000 : ℝ)|^4323 ≤ (10733097395751/25000000000000 : ℝ)^3299
        have hw : |(2622637109/5000000000 : ℝ)|=(2622637109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s8_1 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-405196239/2000000000 : ℝ)*x 0 + (2622935211/5000000000 : ℝ)*x 1 + (169093103/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (405196239/2000000000 : ℝ)^4323 ≤ (6171447846411/50000000000000 : ℝ)^3299 := by
    have hnat : (405196239 : ℕ)^4323*50000000000000^3299 ≤ 6171447846411^3299*2000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405196239 2000000000 6171447846411 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622935211/5000000000 : ℝ)^4323 ≤ (42938784314743/100000000000000 : ℝ)^3299 := by
    have hnat : (2622935211 : ℕ)^4323*100000000000000^3299 ≤ 42938784314743^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622935211 5000000000 42938784314743 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169093103/312500000 : ℝ)^4323 ≤ (5589789996043/12500000000000 : ℝ)^3299 := by
    have hnat : (169093103 : ℕ)^4323*12500000000000^3299 ≤ 5589789996043^3299*312500000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169093103 312500000 5589789996043 12500000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-405196239/2000000000 : ℝ), (2622935211/5000000000 : ℝ), (169093103/312500000 : ℝ)] ![(6171447846411/50000000000000 : ℝ), (42938784314743/100000000000000 : ℝ), (5589789996043/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-405196239/2000000000 : ℝ)|^4323 ≤ (6171447846411/50000000000000 : ℝ)^3299
        have hw : |(-405196239/2000000000 : ℝ)|=(405196239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622935211/5000000000 : ℝ)|^4323 ≤ (42938784314743/100000000000000 : ℝ)^3299
        have hw : |(2622935211/5000000000 : ℝ)|=(2622935211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169093103/312500000 : ℝ)|^4323 ≤ (5589789996043/12500000000000 : ℝ)^3299
        have hw : |(169093103/312500000 : ℝ)|=(169093103/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s8_2 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (331604783/625000000 : ℝ)*x 0 + (-972489869/5000000000 : ℝ)*x 1 + (5410979633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331604783/625000000 : ℝ)^4323 ≤ (21790696339807/50000000000000 : ℝ)^3299 := by
    have hnat : (331604783 : ℕ)^4323*50000000000000^3299 ≤ 21790696339807^3299*625000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331604783 625000000 21790696339807 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (972489869/5000000000 : ℝ)^4323 ≤ (1462535460989/12500000000000 : ℝ)^3299 := by
    have hnat : (972489869 : ℕ)^4323*12500000000000^3299 ≤ 1462535460989^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      972489869 5000000000 1462535460989 12500000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410979633/10000000000 : ℝ)^4323 ≤ (69872380653/156250000000 : ℝ)^3299 := by
    have hnat : (5410979633 : ℕ)^4323*156250000000^3299 ≤ 69872380653^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410979633 10000000000 69872380653 156250000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331604783/625000000 : ℝ), (-972489869/5000000000 : ℝ), (5410979633/10000000000 : ℝ)] ![(21790696339807/50000000000000 : ℝ), (1462535460989/12500000000000 : ℝ), (69872380653/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331604783/625000000 : ℝ)|^4323 ≤ (21790696339807/50000000000000 : ℝ)^3299
        have hw : |(331604783/625000000 : ℝ)|=(331604783/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-972489869/5000000000 : ℝ)|^4323 ≤ (1462535460989/12500000000000 : ℝ)^3299
        have hw : |(-972489869/5000000000 : ℝ)|=(972489869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410979633/10000000000 : ℝ)|^4323 ≤ (69872380653/156250000000 : ℝ)^3299
        have hw : |(5410979633/10000000000 : ℝ)|=(5410979633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s8_3 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305676789/10000000000 : ℝ)*x 0 + (270548967/500000000 : ℝ)*x 1 + (-388995957/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305676789/10000000000 : ℝ)^4323 ≤ (871627909779/2000000000000 : ℝ)^3299 := by
    have hnat : (5305676789 : ℕ)^4323*2000000000000^3299 ≤ 871627909779^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305676789 10000000000 871627909779 2000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (270548967/500000000 : ℝ)^4323 ≤ (44718320444847/100000000000000 : ℝ)^3299 := by
    have hnat : (270548967 : ℕ)^4323*100000000000000^3299 ≤ 44718320444847^3299*500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270548967 500000000 44718320444847 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (388995957/2000000000 : ℝ)^4323 ≤ (11700284058407/100000000000000 : ℝ)^3299 := by
    have hnat : (388995957 : ℕ)^4323*100000000000000^3299 ≤ 11700284058407^3299*2000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388995957 2000000000 11700284058407 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305676789/10000000000 : ℝ), (270548967/500000000 : ℝ), (-388995957/2000000000 : ℝ)] ![(871627909779/2000000000000 : ℝ), (44718320444847/100000000000000 : ℝ), (11700284058407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305676789/10000000000 : ℝ)|^4323 ≤ (871627909779/2000000000000 : ℝ)^3299
        have hw : |(5305676789/10000000000 : ℝ)|=(5305676789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(270548967/500000000 : ℝ)|^4323 ≤ (44718320444847/100000000000000 : ℝ)^3299
        have hw : |(270548967/500000000 : ℝ)|=(270548967/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-388995957/2000000000 : ℝ)|^4323 ≤ (11700284058407/100000000000000 : ℝ)^3299
        have hw : |(-388995957/2000000000 : ℝ)|=(388995957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s8_4 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (270074159/625000000 : ℝ)*x 0 + (2249374347/5000000000 : ℝ)*x 1 + (166007283/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270074159/625000000 : ℝ)^4323 ≤ (8325978018617/25000000000000 : ℝ)^3299 := by
    have hnat : (270074159 : ℕ)^4323*25000000000000^3299 ≤ 8325978018617^3299*625000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270074159 625000000 8325978018617 25000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2249374347/5000000000 : ℝ)^4323 ≤ (2194281969581/6250000000000 : ℝ)^3299 := by
    have hnat : (2249374347 : ℕ)^4323*6250000000000^3299 ≤ 2194281969581^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2249374347 5000000000 2194281969581 6250000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (166007283/400000000 : ℝ)^4323 ≤ (1974223524253/6250000000000 : ℝ)^3299 := by
    have hnat : (166007283 : ℕ)^4323*6250000000000^3299 ≤ 1974223524253^3299*400000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166007283 400000000 1974223524253 6250000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270074159/625000000 : ℝ), (2249374347/5000000000 : ℝ), (166007283/400000000 : ℝ)] ![(8325978018617/25000000000000 : ℝ), (2194281969581/6250000000000 : ℝ), (1974223524253/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270074159/625000000 : ℝ)|^4323 ≤ (8325978018617/25000000000000 : ℝ)^3299
        have hw : |(270074159/625000000 : ℝ)|=(270074159/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2249374347/5000000000 : ℝ)|^4323 ≤ (2194281969581/6250000000000 : ℝ)^3299
        have hw : |(2249374347/5000000000 : ℝ)|=(2249374347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(166007283/400000000 : ℝ)|^4323 ≤ (1974223524253/6250000000000 : ℝ)^3299
        have hw : |(166007283/400000000 : ℝ)|=(166007283/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1363_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155556687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (92/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5599/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5599/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14719/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (92/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5599/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (92/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5599/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (92/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5599/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (92/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5599/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (92/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5599/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (92/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5599/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5599/50000 : ℝ) ^ (2161/512 : ℝ) ≤ (9698491319400753/100000000000000000000 : ℝ) := by
    have hpowers : (5599/50000 : ℝ)^2161 ≤ (9698491319400753/100000000000000000000 : ℝ)^512 := by
      have hnat : (5599 : ℕ)^2161*100000000000000000000^512 ≤ 9698491319400753^512*50000^2161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5599 50000 9698491319400753 100000000000000000000 2161 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5599/50000 : ℝ)) (X := (9698491319400753/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hpowhi : (92/625 : ℝ) ^ (2161/512 : ℝ) ≤ (30759968995677801/100000000000000000000 : ℝ) := by
    have hpowers : (92/625 : ℝ)^2161 ≤ (30759968995677801/100000000000000000000 : ℝ)^512 := by
      have hnat : (92 : ℕ)^2161*100000000000000000000^512 ≤ 30759968995677801^512*625^2161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        92 625 30759968995677801 100000000000000000000 2161 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (92/625 : ℝ)) (X := (30759968995677801/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009698491319400753/50000000000000000000 : ℝ) ≤ (312514360423729/312500000000000 : ℝ) ^ (2161/512 : ℝ) := by
    have hpowers : (50009698491319400753/50000000000000000000 : ℝ)^512 ≤ (312514360423729/312500000000000 : ℝ)^2161 := by
      have hnat : (50009698491319400753 : ℕ)^512*312500000000000^2161 ≤ 312514360423729^2161*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009698491319400753 50000000000000000000 312514360423729 312500000000000 512 2161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312514360423729/312500000000000 : ℝ)) (X := (50009698491319400753/50000000000000000000 : ℝ)) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020229230157539277/50000000000000000000 : ℝ) ≤ (5000479211819489/5000000000000000 : ℝ) ^ (2161/512 : ℝ) := by
    have hpowers : (50020229230157539277/50000000000000000000 : ℝ)^512 ≤ (5000479211819489/5000000000000000 : ℝ)^2161 := by
      have hnat : (50020229230157539277 : ℕ)^512*5000000000000000^2161 ≤ 5000479211819489^2161*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020229230157539277 50000000000000000000 5000479211819489 5000000000000000 512 2161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000479211819489/5000000000000000 : ℝ)) (X := (50020229230157539277/50000000000000000000 : ℝ)) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030759968995677801/50000000000000000000 : ℝ) ≤ (2500364328429657/2500000000000000 : ℝ) ^ (2161/512 : ℝ) := by
    have hpowers : (50030759968995677801/50000000000000000000 : ℝ)^512 ≤ (2500364328429657/2500000000000000 : ℝ)^2161 := by
      have hnat : (50030759968995677801 : ℕ)^512*2500000000000000^2161 ≤ 2500364328429657^2161*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030759968995677801 50000000000000000000 2500364328429657 2500000000000000 512 2161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500364328429657/2500000000000000 : ℝ)) (X := (50030759968995677801/50000000000000000000 : ℝ)) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9698491319400753/100000000000000000000 : ℝ) ≤ ((4401305666871513977/4402500000000000000 : ℝ)+2*(9977801593/7044000000000 : ℝ)*(5599/50000 : ℝ))^(2161/512 : ℝ) := by
    rw [show (4401305666871513977/4402500000000000000 : ℝ)+2*(9977801593/7044000000000 : ℝ)*(5599/50000 : ℝ)=(312514360423729/312500000000000 : ℝ) by norm_num, show 1+2*(9698491319400753/100000000000000000000 : ℝ)=(50009698491319400753/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30759968995677801/100000000000000000000 : ℝ)+(9698491319400753/100000000000000000000 : ℝ) ≤ ((4401305666871513977/4402500000000000000 : ℝ)+(9977801593/7044000000000 : ℝ)*((92/625 : ℝ)+(5599/50000 : ℝ)))^(2161/512 : ℝ) := by
    rw [show (4401305666871513977/4402500000000000000 : ℝ)+(9977801593/7044000000000 : ℝ)*((92/625 : ℝ)+(5599/50000 : ℝ))=(5000479211819489/5000000000000000 : ℝ) by norm_num, show 1+(30759968995677801/100000000000000000000 : ℝ)+(9698491319400753/100000000000000000000 : ℝ)=(50020229230157539277/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30759968995677801/100000000000000000000 : ℝ) ≤ ((4401305666871513977/4402500000000000000 : ℝ)+2*(9977801593/7044000000000 : ℝ)*(92/625 : ℝ))^(2161/512 : ℝ) := by
    rw [show (4401305666871513977/4402500000000000000 : ℝ)+2*(9977801593/7044000000000 : ℝ)*(92/625 : ℝ)=(2500364328429657/2500000000000000 : ℝ) by norm_num, show 1+2*(30759968995677801/100000000000000000000 : ℝ)=(50030759968995677801/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4401305666871513977/4402500000000000000 : ℝ)*(X 1 0+X 2 0)+(9977801593/7044000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2161/512 : ℝ)) (lo := (5599/50000 : ℝ)) (hi := (92/625 : ℝ)) (c := (4401305666871513977/4402500000000000000 : ℝ)) (alpha := (9977801593/7044000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4401305666871513977/4402500000000000000 : ℝ)*(X 0 1+X 2 1)+(9977801593/7044000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2161/512 : ℝ)) (lo := (5599/50000 : ℝ)) (hi := (92/625 : ℝ)) (c := (4401305666871513977/4402500000000000000 : ℝ)) (alpha := (9977801593/7044000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4401305666871513977/4402500000000000000 : ℝ)*(X 0 2+X 1 2)+(9977801593/7044000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2161/512 : ℝ)) (lo := (5599/50000 : ℝ)) (hi := (92/625 : ℝ)) (c := (4401305666871513977/4402500000000000000 : ℝ)) (alpha := (9977801593/7044000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5348614749/10000000000 : ℝ)*X 1 0+(-527671287/2500000000 : ℝ)*X 1 1+(2622637109/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s8_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-405196239/2000000000 : ℝ)*X 0 0+(2622935211/5000000000 : ℝ)*X 0 1+(169093103/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s8_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((331604783/625000000 : ℝ)*X 1 0+(-972489869/5000000000 : ℝ)*X 1 1+(5410979633/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s8_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5305676789/10000000000 : ℝ)*X 2 0+(270548967/500000000 : ℝ)*X 2 1+(-388995957/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s8_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((270074159/625000000 : ℝ)*X 0 0+(2249374347/5000000000 : ℝ)*X 0 1+(166007283/400000000 : ℝ)*X 0 2+(270074159/625000000 : ℝ)*X 1 0+(2249374347/5000000000 : ℝ)*X 1 1+(166007283/400000000 : ℝ)*X 1 2+(270074159/625000000 : ℝ)*X 2 0+(2249374347/5000000000 : ℝ)*X 2 1+(166007283/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s8_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28408934300170927615161067/18343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (235877193/25000000000000 : ℝ)*(base19) + (1358917363/100000000000000 : ℝ)*(base23) + (528785317/100000000000000 : ℝ)*(lower1) + (51819171/50000000000000 : ℝ)*(upper3) + (63533459/100000000000000 : ℝ)*(lower4) + (732153/400000000000 : ℝ)*(upper5) + (2231364409298171/50000000000000 : ℝ)*(major0) + (2231364409298171/50000000000000 : ℝ)*(major1) + (2231364409298171/50000000000000 : ℝ)*(major2) + (281296163/100000000000000 : ℝ)*(sp0) + (3028290677438253/50000000000000 : ℝ)*(sp1) + (6056580130071571/100000000000000 : ℝ)*(sp2) + (3028289997979571/50000000000000 : ℝ)*(sp3) + (1434438115346447/50000000000000 : ℝ)*(sp4) + (1434438115346447/50000000000000 : ℝ)*(f.failure) + (3028290677438253/50000000000000 : ℝ)*(f.sum) + (2087824025449/440250000000000000000000000 : ℝ)*base66 + (892424388805696311/73375000000000000000000000000000 : ℝ)*base68 + (234838288761446311/73375000000000000000000000000000 : ℝ)*base70 + (917212367373321311/73375000000000000000000000000000 : ℝ)*base72 + (77356912381/440250000000000000000000000 : ℝ)*base74 + (258077560134821311/73375000000000000000000000000000 : ℝ)*base76 + (625771377220946311/73375000000000000000000000000000 : ℝ)*base78 + (387380838809803689/73375000000000000000000000000000 : ℝ)*base79 + (185638386253/35220000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (52541089/5000000000000000000000 : ℝ)*base89 + (52541089/5000000000000000000000 : ℝ)*base91 + (52541089/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1363_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155556687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (92/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5599/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5599/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14719/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1363_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1363_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155556687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14727/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11191/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5599/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14719/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1363_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1363_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1363_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155556687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14727/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11191/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5599/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14719/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1363_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
