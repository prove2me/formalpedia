-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1337_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:03:23.687864+00:00
-- url     : https://prove2.me/submissions/3dc56e48-eb03-4bc2-b331-85aea6472ae5

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
theorem support_rectangle_w1337_s3_0 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2046486159/10000000000 : ℝ)*x 0 + (1356953399/2500000000 : ℝ)*x 1 + (5230794969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2046486159/10000000000 : ℝ)^4297 ≤ (3114505458493/25000000000000 : ℝ)^3273 := by
    have hnat : (2046486159 : ℕ)^4297*25000000000000^3273 ≤ 3114505458493^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046486159 10000000000 3114505458493 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356953399/2500000000 : ℝ)^4297 ≤ (11208279168767/25000000000000 : ℝ)^3273 := by
    have hnat : (1356953399 : ℕ)^4297*25000000000000^3273 ≤ 11208279168767^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356953399 2500000000 11208279168767 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5230794969/10000000000 : ℝ)^4297 ≤ (21354430743667/50000000000000 : ℝ)^3273 := by
    have hnat : (5230794969 : ℕ)^4297*50000000000000^3273 ≤ 21354430743667^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230794969 10000000000 21354430743667 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2046486159/10000000000 : ℝ), (1356953399/2500000000 : ℝ), (5230794969/10000000000 : ℝ)] ![(3114505458493/25000000000000 : ℝ), (11208279168767/25000000000000 : ℝ), (21354430743667/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2046486159/10000000000 : ℝ)|^4297 ≤ (3114505458493/25000000000000 : ℝ)^3273
        have hw : |(-2046486159/10000000000 : ℝ)|=(2046486159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356953399/2500000000 : ℝ)|^4297 ≤ (11208279168767/25000000000000 : ℝ)^3273
        have hw : |(1356953399/2500000000 : ℝ)|=(1356953399/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5230794969/10000000000 : ℝ)|^4297 ≤ (21354430743667/50000000000000 : ℝ)^3273
        have hw : |(5230794969/10000000000 : ℝ)|=(5230794969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s3_1 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352867553/10000000000 : ℝ)*x 0 + (-2147190061/10000000000 : ℝ)*x 1 + (1307698761/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352867553/10000000000 : ℝ)^4297 ≤ (4402215562773/10000000000000 : ℝ)^3273 := by
    have hnat : (5352867553 : ℕ)^4297*10000000000000^3273 ≤ 4402215562773^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352867553 10000000000 4402215562773 10000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2147190061/10000000000 : ℝ)^4297 ≤ (3317245516003/25000000000000 : ℝ)^3273 := by
    have hnat : (2147190061 : ℕ)^4297*25000000000000^3273 ≤ 3317245516003^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147190061 10000000000 3317245516003 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307698761/2500000000 : ℝ)^4297 ≤ (42708862291287/100000000000000 : ℝ)^3273 := by
    have hnat : (1307698761 : ℕ)^4297*100000000000000^3273 ≤ 42708862291287^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307698761 2500000000 42708862291287 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352867553/10000000000 : ℝ), (-2147190061/10000000000 : ℝ), (1307698761/2500000000 : ℝ)] ![(4402215562773/10000000000000 : ℝ), (3317245516003/25000000000000 : ℝ), (42708862291287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352867553/10000000000 : ℝ)|^4297 ≤ (4402215562773/10000000000000 : ℝ)^3273
        have hw : |(5352867553/10000000000 : ℝ)|=(5352867553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2147190061/10000000000 : ℝ)|^4297 ≤ (3317245516003/25000000000000 : ℝ)^3273
        have hw : |(-2147190061/10000000000 : ℝ)|=(2147190061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307698761/2500000000 : ℝ)|^4297 ≤ (42708862291287/100000000000000 : ℝ)^3273
        have hw : |(1307698761/2500000000 : ℝ)|=(1307698761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s3_2 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676433667/5000000000 : ℝ)*x 0 + (2615397653/5000000000 : ℝ)*x 1 + (-1073595003/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676433667/5000000000 : ℝ)^4297 ≤ (44022153263181/100000000000000 : ℝ)^3273 := by
    have hnat : (2676433667 : ℕ)^4297*100000000000000^3273 ≤ 44022153263181^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676433667 5000000000 44022153263181 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2615397653/5000000000 : ℝ)^4297 ≤ (10677216274941/25000000000000 : ℝ)^3273 := by
    have hnat : (2615397653 : ℕ)^4297*25000000000000^3273 ≤ 10677216274941^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2615397653 5000000000 10677216274941 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1073595003/5000000000 : ℝ)^4297 ≤ (103663918889/781250000000 : ℝ)^3273 := by
    have hnat : (1073595003 : ℕ)^4297*781250000000^3273 ≤ 103663918889^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073595003 5000000000 103663918889 781250000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676433667/5000000000 : ℝ), (2615397653/5000000000 : ℝ), (-1073595003/5000000000 : ℝ)] ![(44022153263181/100000000000000 : ℝ), (10677216274941/25000000000000 : ℝ), (103663918889/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676433667/5000000000 : ℝ)|^4297 ≤ (44022153263181/100000000000000 : ℝ)^3273
        have hw : |(2676433667/5000000000 : ℝ)|=(2676433667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2615397653/5000000000 : ℝ)|^4297 ≤ (10677216274941/25000000000000 : ℝ)^3273
        have hw : |(2615397653/5000000000 : ℝ)|=(2615397653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1073595003/5000000000 : ℝ)|^4297 ≤ (103663918889/781250000000 : ℝ)^3273
        have hw : |(-1073595003/5000000000 : ℝ)|=(1073595003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s3_3 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4326832801/10000000000 : ℝ)*x 0 + (1031368651/2500000000 : ℝ)*x 1 + (4537367943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4326832801/10000000000 : ℝ)^4297 ≤ (33292106106927/100000000000000 : ℝ)^3273 := by
    have hnat : (4326832801 : ℕ)^4297*100000000000000^3273 ≤ 33292106106927^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326832801 10000000000 33292106106927 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1031368651/2500000000 : ℝ)^4297 ≤ (15636516558943/50000000000000 : ℝ)^3273 := by
    have hnat : (1031368651 : ℕ)^4297*50000000000000^3273 ≤ 15636516558943^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031368651 2500000000 15636516558943 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4537367943/10000000000 : ℝ)^4297 ≤ (4429357594819/12500000000000 : ℝ)^3273 := by
    have hnat : (4537367943 : ℕ)^4297*12500000000000^3273 ≤ 4429357594819^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4537367943 10000000000 4429357594819 12500000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4326832801/10000000000 : ℝ), (1031368651/2500000000 : ℝ), (4537367943/10000000000 : ℝ)] ![(33292106106927/100000000000000 : ℝ), (15636516558943/50000000000000 : ℝ), (4429357594819/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4326832801/10000000000 : ℝ)|^4297 ≤ (33292106106927/100000000000000 : ℝ)^3273
        have hw : |(4326832801/10000000000 : ℝ)|=(4326832801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1031368651/2500000000 : ℝ)|^4297 ≤ (15636516558943/50000000000000 : ℝ)^3273
        have hw : |(1031368651/2500000000 : ℝ)|=(1031368651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4537367943/10000000000 : ℝ)|^4297 ≤ (4429357594819/12500000000000 : ℝ)^3273
        have hw : |(4537367943/10000000000 : ℝ)|=(4537367943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s3_4 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2046505651/10000000000 : ℝ)*x 0 + (5231618589/10000000000 : ℝ)*x 1 + (5426985041/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2046505651/10000000000 : ℝ)^4297 ≤ (3114544403939/25000000000000 : ℝ)^3273 := by
    have hnat : (2046505651 : ℕ)^4297*25000000000000^3273 ≤ 3114544403939^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2046505651 10000000000 3114544403939 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5231618589/10000000000 : ℝ)^4297 ≤ (8543538080021/20000000000000 : ℝ)^3273 := by
    have hnat : (5231618589 : ℕ)^4297*20000000000000^3273 ≤ 8543538080021^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231618589 10000000000 8543538080021 20000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426985041/10000000000 : ℝ)^4297 ≤ (8964826391929/20000000000000 : ℝ)^3273 := by
    have hnat : (5426985041 : ℕ)^4297*20000000000000^3273 ≤ 8964826391929^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426985041 10000000000 8964826391929 20000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2046505651/10000000000 : ℝ), (5231618589/10000000000 : ℝ), (5426985041/10000000000 : ℝ)] ![(3114544403939/25000000000000 : ℝ), (8543538080021/20000000000000 : ℝ), (8964826391929/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2046505651/10000000000 : ℝ)|^4297 ≤ (3114544403939/25000000000000 : ℝ)^3273
        have hw : |(-2046505651/10000000000 : ℝ)|=(2046505651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5231618589/10000000000 : ℝ)|^4297 ≤ (8543538080021/20000000000000 : ℝ)^3273
        have hw : |(5231618589/10000000000 : ℝ)|=(5231618589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426985041/10000000000 : ℝ)|^4297 ≤ (8964826391929/20000000000000 : ℝ)^3273
        have hw : |(5426985041/10000000000 : ℝ)|=(5426985041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s3_5 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (13255369/25000000 : ℝ)*x 0 + (-1951000091/10000000000 : ℝ)*x 1 + (1085397063/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13255369/25000000 : ℝ)^4297 ≤ (8695068888347/20000000000000 : ℝ)^3273 := by
    have hnat : (13255369 : ℕ)^4297*20000000000000^3273 ≤ 8695068888347^3273*25000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13255369 25000000 8695068888347 20000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1951000091/10000000000 : ℝ)^4297 ≤ (11700520610519/100000000000000 : ℝ)^3273 := by
    have hnat : (1951000091 : ℕ)^4297*100000000000000^3273 ≤ 11700520610519^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1951000091 10000000000 11700520610519 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085397063/2000000000 : ℝ)^4297 ≤ (8964826986157/20000000000000 : ℝ)^3273 := by
    have hnat : (1085397063 : ℕ)^4297*20000000000000^3273 ≤ 8964826986157^3273*2000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085397063 2000000000 8964826986157 20000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13255369/25000000 : ℝ), (-1951000091/10000000000 : ℝ), (1085397063/2000000000 : ℝ)] ![(8695068888347/20000000000000 : ℝ), (11700520610519/100000000000000 : ℝ), (8964826986157/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13255369/25000000 : ℝ)|^4297 ≤ (8695068888347/20000000000000 : ℝ)^3273
        have hw : |(13255369/25000000 : ℝ)|=(13255369/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1951000091/10000000000 : ℝ)|^4297 ≤ (11700520610519/100000000000000 : ℝ)^3273
        have hw : |(-1951000091/10000000000 : ℝ)|=(1951000091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085397063/2000000000 : ℝ)|^4297 ≤ (8964826986157/20000000000000 : ℝ)^3273
        have hw : |(1085397063/2000000000 : ℝ)|=(1085397063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s3_6 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5302148427/10000000000 : ℝ)*x 0 + (339186549/625000000 : ℝ)*x 1 + (-487749923/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302148427/10000000000 : ℝ)^4297 ≤ (43475353344319/100000000000000 : ℝ)^3273 := by
    have hnat : (5302148427 : ℕ)^4297*100000000000000^3273 ≤ 43475353344319^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302148427 10000000000 43475353344319 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339186549/625000000 : ℝ)^4297 ≤ (8964825834569/20000000000000 : ℝ)^3273 := by
    have hnat : (339186549 : ℕ)^4297*20000000000000^3273 ≤ 8964825834569^3273*625000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339186549 625000000 8964825834569 20000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (487749923/2500000000 : ℝ)^4297 ≤ (11700517468997/100000000000000 : ℝ)^3273 := by
    have hnat : (487749923 : ℕ)^4297*100000000000000^3273 ≤ 11700517468997^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487749923 2500000000 11700517468997 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302148427/10000000000 : ℝ), (339186549/625000000 : ℝ), (-487749923/2500000000 : ℝ)] ![(43475353344319/100000000000000 : ℝ), (8964825834569/20000000000000 : ℝ), (11700517468997/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302148427/10000000000 : ℝ)|^4297 ≤ (43475353344319/100000000000000 : ℝ)^3273
        have hw : |(5302148427/10000000000 : ℝ)|=(5302148427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339186549/625000000 : ℝ)|^4297 ≤ (8964825834569/20000000000000 : ℝ)^3273
        have hw : |(339186549/625000000 : ℝ)|=(339186549/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-487749923/2500000000 : ℝ)|^4297 ≤ (11700517468997/100000000000000 : ℝ)^3273
        have hw : |(-487749923/2500000000 : ℝ)|=(487749923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s3_7 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4326874441/10000000000 : ℝ)*x 0 + (1133911489/2500000000 : ℝ)*x 1 + (1031801537/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4326874441/10000000000 : ℝ)^4297 ≤ (33292526738511/100000000000000 : ℝ)^3273 := by
    have hnat : (4326874441 : ℕ)^4297*100000000000000^3273 ≤ 33292526738511^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326874441 10000000000 33292526738511 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1133911489/2500000000 : ℝ)^4297 ≤ (35417206472347/100000000000000 : ℝ)^3273 := by
    have hnat : (1133911489 : ℕ)^4297*100000000000000^3273 ≤ 35417206472347^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133911489 2500000000 35417206472347 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1031801537/2500000000 : ℝ)^4297 ≤ (15645133388097/50000000000000 : ℝ)^3273 := by
    have hnat : (1031801537 : ℕ)^4297*50000000000000^3273 ≤ 15645133388097^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031801537 2500000000 15645133388097 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4326874441/10000000000 : ℝ), (1133911489/2500000000 : ℝ), (1031801537/2500000000 : ℝ)] ![(33292526738511/100000000000000 : ℝ), (35417206472347/100000000000000 : ℝ), (15645133388097/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4326874441/10000000000 : ℝ)|^4297 ≤ (33292526738511/100000000000000 : ℝ)^3273
        have hw : |(4326874441/10000000000 : ℝ)|=(4326874441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1133911489/2500000000 : ℝ)|^4297 ≤ (35417206472347/100000000000000 : ℝ)^3273
        have hw : |(1133911489/2500000000 : ℝ)|=(1133911489/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1031801537/2500000000 : ℝ)|^4297 ≤ (15645133388097/50000000000000 : ℝ)^3273
        have hw : |(1031801537/2500000000 : ℝ)|=(1031801537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1337_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154531637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4031/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9819/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2169/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7507/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4031/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9819/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4031/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9819/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4031/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9819/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4031/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9819/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4031/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9819/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4031/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9819/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9819/100000 : ℝ) ^ (537/128 : ℝ) ≤ (1181509376337973/20000000000000000000 : ℝ) := by
    have hpowers : (9819/100000 : ℝ)^537 ≤ (1181509376337973/20000000000000000000 : ℝ)^128 := by
      have hnat : (9819 : ℕ)^537*20000000000000000000^128 ≤ 1181509376337973^128*100000^537 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9819 100000 1181509376337973 20000000000000000000 537 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9819/100000 : ℝ)) (X := (1181509376337973/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hpowhi : (4031/25000 : ℝ) ^ (537/128 : ℝ) ≤ (591576209223563/1250000000000000000 : ℝ) := by
    have hpowers : (4031/25000 : ℝ)^537 ≤ (591576209223563/1250000000000000000 : ℝ)^128 := by
      have hnat : (4031 : ℕ)^537*1250000000000000000^128 ≤ 591576209223563^128*25000^537 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4031 25000 591576209223563 1250000000000000000 537 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4031/25000 : ℝ)) (X := (591576209223563/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001181509376337973/10000000000000000000 : ℝ) ≤ (625017600837527/625000000000000 : ℝ) ^ (537/128 : ℝ) := by
    have hpowers : (10001181509376337973/10000000000000000000 : ℝ)^128 ≤ (625017600837527/625000000000000 : ℝ)^537 := by
      have hnat : (10001181509376337973 : ℕ)^128*625000000000000^537 ≤ 625017600837527^537*10000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001181509376337973 10000000000000000000 625017600837527 625000000000000 128 537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625017600837527/625000000000000 : ℝ)) (X := (10001181509376337973/10000000000000000000 : ℝ)) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010646728723914981/20000000000000000000 : ℝ) ≤ (5000634313358699/5000000000000000 : ℝ) ^ (537/128 : ℝ) := by
    have hpowers : (20010646728723914981/20000000000000000000 : ℝ)^128 ≤ (5000634313358699/5000000000000000 : ℝ)^537 := by
      have hnat : (20010646728723914981 : ℕ)^128*5000000000000000^537 ≤ 5000634313358699^537*20000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010646728723914981 20000000000000000000 5000634313358699 5000000000000000 128 537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000634313358699/5000000000000000 : ℝ)) (X := (20010646728723914981/20000000000000000000 : ℝ)) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (625591576209223563/625000000000000000 : ℝ) ≤ (2500563910008591/2500000000000000 : ℝ) ^ (537/128 : ℝ) := by
    have hpowers : (625591576209223563/625000000000000000 : ℝ)^128 ≤ (2500563910008591/2500000000000000 : ℝ)^537 := by
      have hnat : (625591576209223563 : ℕ)^128*2500000000000000^537 ≤ 2500563910008591^537*625000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625591576209223563 625000000000000000 2500563910008591 2500000000000000 128 537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500563910008591/2500000000000000 : ℝ)) (X := (625591576209223563/625000000000000000 : ℝ)) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1181509376337973/20000000000000000000 : ℝ) ≤ ((15758098151242786363/15762500000000000000 : ℝ)+2*(493506658483/315250000000000 : ℝ)*(9819/100000 : ℝ))^(537/128 : ℝ) := by
    rw [show (15758098151242786363/15762500000000000000 : ℝ)+2*(493506658483/315250000000000 : ℝ)*(9819/100000 : ℝ)=(625017600837527/625000000000000 : ℝ) by norm_num, show 1+2*(1181509376337973/20000000000000000000 : ℝ)=(10001181509376337973/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(591576209223563/1250000000000000000 : ℝ)+(1181509376337973/20000000000000000000 : ℝ) ≤ ((15758098151242786363/15762500000000000000 : ℝ)+(493506658483/315250000000000 : ℝ)*((4031/25000 : ℝ)+(9819/100000 : ℝ)))^(537/128 : ℝ) := by
    rw [show (15758098151242786363/15762500000000000000 : ℝ)+(493506658483/315250000000000 : ℝ)*((4031/25000 : ℝ)+(9819/100000 : ℝ))=(5000634313358699/5000000000000000 : ℝ) by norm_num, show 1+(591576209223563/1250000000000000000 : ℝ)+(1181509376337973/20000000000000000000 : ℝ)=(20010646728723914981/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(591576209223563/1250000000000000000 : ℝ) ≤ ((15758098151242786363/15762500000000000000 : ℝ)+2*(493506658483/315250000000000 : ℝ)*(4031/25000 : ℝ))^(537/128 : ℝ) := by
    rw [show (15758098151242786363/15762500000000000000 : ℝ)+2*(493506658483/315250000000000 : ℝ)*(4031/25000 : ℝ)=(2500563910008591/2500000000000000 : ℝ) by norm_num, show 1+2*(591576209223563/1250000000000000000 : ℝ)=(625591576209223563/625000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (15758098151242786363/15762500000000000000 : ℝ)*(X 1 0+X 2 0)+(493506658483/315250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (537/128 : ℝ)) (lo := (9819/100000 : ℝ)) (hi := (4031/25000 : ℝ)) (c := (15758098151242786363/15762500000000000000 : ℝ)) (alpha := (493506658483/315250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (15758098151242786363/15762500000000000000 : ℝ)*(X 0 1+X 2 1)+(493506658483/315250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (537/128 : ℝ)) (lo := (9819/100000 : ℝ)) (hi := (4031/25000 : ℝ)) (c := (15758098151242786363/15762500000000000000 : ℝ)) (alpha := (493506658483/315250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (15758098151242786363/15762500000000000000 : ℝ)*(X 0 2+X 1 2)+(493506658483/315250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (537/128 : ℝ)) (lo := (9819/100000 : ℝ)) (hi := (4031/25000 : ℝ)) (c := (15758098151242786363/15762500000000000000 : ℝ)) (alpha := (493506658483/315250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2046486159/10000000000 : ℝ)*X 0 0+(1356953399/2500000000 : ℝ)*X 0 1+(5230794969/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352867553/10000000000 : ℝ)*X 1 0+(-2147190061/10000000000 : ℝ)*X 1 1+(1307698761/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676433667/5000000000 : ℝ)*X 2 0+(2615397653/5000000000 : ℝ)*X 2 1+(-1073595003/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4326832801/10000000000 : ℝ)*X 0 0+(1031368651/2500000000 : ℝ)*X 0 1+(4537367943/10000000000 : ℝ)*X 0 2+(4326832801/10000000000 : ℝ)*X 1 0+(1031368651/2500000000 : ℝ)*X 1 1+(4537367943/10000000000 : ℝ)*X 1 2+(4326832801/10000000000 : ℝ)*X 2 0+(1031368651/2500000000 : ℝ)*X 2 1+(4537367943/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2046505651/10000000000 : ℝ)*X 0 0+(5231618589/10000000000 : ℝ)*X 0 1+(5426985041/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((13255369/25000000 : ℝ)*X 1 0+(-1951000091/10000000000 : ℝ)*X 1 1+(1085397063/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302148427/10000000000 : ℝ)*X 2 0+(339186549/625000000 : ℝ)*X 2 1+(-487749923/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4326874441/10000000000 : ℝ)*X 0 0+(1133911489/2500000000 : ℝ)*X 0 1+(1031801537/2500000000 : ℝ)*X 0 2+(4326874441/10000000000 : ℝ)*X 1 0+(1133911489/2500000000 : ℝ)*X 1 1+(1031801537/2500000000 : ℝ)*X 1 2+(4326874441/10000000000 : ℝ)*X 2 0+(1133911489/2500000000 : ℝ)*X 2 1+(1031801537/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (466437655784067273293153589/49257812500000000000000000000000 : ℝ) := by norm_num
    linear_combination (845265907/50000000000000 : ℝ)*(base19) + (145267021/10000000000000 : ℝ)*(base23) + (212167273/100000000000000 : ℝ)*(upper3) + (16165767/100000000000000 : ℝ)*(upper4) + (210966217/100000000000000 : ℝ)*(upper5) + (937946325439623/25000000000000 : ℝ)*(major0) + (937946325439623/25000000000000 : ℝ)*(major1) + (937946325439623/25000000000000 : ℝ)*(major2) + (2537847607681933/50000000000000 : ℝ)*(sp0) + (1015145149226769/20000000000000 : ℝ)*(sp1) + (5075725983995449/100000000000000 : ℝ)*(sp2) + (2427828126711019/100000000000000 : ℝ)*(sp3) + (1006915681/3125000000000 : ℝ)*(sp4) + (588979861/4000000000000 : ℝ)*(sp7) + (303480356400943/12500000000000 : ℝ)*(f.failure) + (5075727436665659/100000000000000 : ℝ)*(f.sum) + (10831988943411/15762500000000000000000000000 : ℝ)*base65 + (2786706456414711149/394062500000000000000000000000000 : ℝ)*base67 + (4812390552845023649/394062500000000000000000000000000 : ℝ)*base69 + (2982916074674398649/394062500000000000000000000000000 : ℝ)*base71 + (87824092747003/31525000000000000000000000000 : ℝ)*base74 + (3099982721715601351/394062500000000000000000000000000 : ℝ)*base76 + (2328326371630336149/394062500000000000000000000000000 : ℝ)*base77 + (3186116869236586149/394062500000000000000000000000000 : ℝ)*base79 + (95824100322303/31525000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (133691/1250000000000000000000 : ℝ)*base89 + (133691/1250000000000000000000 : ℝ)*base91 + (133691/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1552542913984094266336125771/788125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18427711/4000000000000 : ℝ)*(base19) + (1734985057/100000000000000 : ℝ)*(base23) + (22507189/12500000000000 : ℝ)*(upper3) + (29949663/20000000000000 : ℝ)*(lower4) + (3171389/2500000000000 : ℝ)*(upper5) + (3783465830531739/100000000000000 : ℝ)*(major0) + (3783465830531739/100000000000000 : ℝ)*(major1) + (3783465830531739/100000000000000 : ℝ)*(major2) + (4354631727/50000000000000 : ℝ)*(sp1) + (5787448931/20000000000000 : ℝ)*(sp2) + (1023717549113817/20000000000000 : ℝ)*(sp4) + (639822321951607/12500000000000 : ℝ)*(sp5) + (5118557073339373/100000000000000 : ℝ)*(sp6) + (47819215817/1953125000 : ℝ)*(sp7) + (47819215817/1953125000 : ℝ)*(f.failure) + (1023717549113817/20000000000000 : ℝ)*(f.sum) + (7699572459749/31525000000000000000000000000 : ℝ)*base65 + (6146999982158475257/1576250000000000000000000000000000 : ℝ)*base67 + (24356705430866524743/1576250000000000000000000000000000 : ℝ)*base70 + (3614521753862774743/1576250000000000000000000000000000 : ℝ)*base72 + (7786211140453/3940625000000000000000000000 : ℝ)*base73 + (9198971779855274743/1576250000000000000000000000000000 : ℝ)*base76 + (9115417328761524743/1576250000000000000000000000000000 : ℝ)*base78 + (3283002915887225257/1576250000000000000000000000000000 : ℝ)*base79 + (5501372636593/985156250000000000000000000 : ℝ)*base82 + (2443/1562500000000000000 : ℝ)*base90 + (2443/1562500000000000000 : ℝ)*base92 + (2443/1562500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1337_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154531637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4031/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9819/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2169/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7507/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1337_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1337_s4_0 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-20479893/100000000 : ℝ)*x 0 + (5415615457/10000000000 : ℝ)*x 1 + (2621003051/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20479893/100000000 : ℝ)^4297 ≤ (3117509107921/25000000000000 : ℝ)^3273 := by
    have hnat : (20479893 : ℕ)^4297*25000000000000^3273 ≤ 3117509107921^3273*100000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20479893 100000000 3117509107921 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415615457/10000000000 : ℝ)^4297 ≤ (22350442705603/50000000000000 : ℝ)^3273 := by
    have hnat : (5415615457 : ℕ)^4297*50000000000000^3273 ≤ 22350442705603^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415615457 10000000000 22350442705603 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621003051/5000000000 : ℝ)^4297 ≤ (10707269537263/25000000000000 : ℝ)^3273 := by
    have hnat : (2621003051 : ℕ)^4297*25000000000000^3273 ≤ 10707269537263^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621003051 5000000000 10707269537263 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-20479893/100000000 : ℝ), (5415615457/10000000000 : ℝ), (2621003051/5000000000 : ℝ)] ![(3117509107921/25000000000000 : ℝ), (22350442705603/50000000000000 : ℝ), (10707269537263/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-20479893/100000000 : ℝ)|^4297 ≤ (3117509107921/25000000000000 : ℝ)^3273
        have hw : |(-20479893/100000000 : ℝ)|=(20479893/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415615457/10000000000 : ℝ)|^4297 ≤ (22350442705603/50000000000000 : ℝ)^3273
        have hw : |(5415615457/10000000000 : ℝ)|=(5415615457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621003051/5000000000 : ℝ)|^4297 ≤ (10707269537263/25000000000000 : ℝ)^3273
        have hw : |(2621003051/5000000000 : ℝ)|=(2621003051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s4_1 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349760617/10000000000 : ℝ)*x 0 + (-534124701/2500000000 : ℝ)*x 1 + (5242005943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349760617/10000000000 : ℝ)^4297 ≤ (10997153251139/25000000000000 : ℝ)^3273 := by
    have hnat : (5349760617 : ℕ)^4297*25000000000000^3273 ≤ 10997153251139^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349760617 10000000000 10997153251139 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (534124701/2500000000 : ℝ)^4297 ≤ (13182310537539/100000000000000 : ℝ)^3273 := by
    have hnat : (534124701 : ℕ)^4297*100000000000000^3273 ≤ 13182310537539^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534124701 2500000000 13182310537539 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5242005943/10000000000 : ℝ)^4297 ≤ (42829076443529/100000000000000 : ℝ)^3273 := by
    have hnat : (5242005943 : ℕ)^4297*100000000000000^3273 ≤ 42829076443529^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242005943 10000000000 42829076443529 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349760617/10000000000 : ℝ), (-534124701/2500000000 : ℝ), (5242005943/10000000000 : ℝ)] ![(10997153251139/25000000000000 : ℝ), (13182310537539/100000000000000 : ℝ), (42829076443529/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349760617/10000000000 : ℝ)|^4297 ≤ (10997153251139/25000000000000 : ℝ)^3273
        have hw : |(5349760617/10000000000 : ℝ)|=(5349760617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-534124701/2500000000 : ℝ)|^4297 ≤ (13182310537539/100000000000000 : ℝ)^3273
        have hw : |(-534124701/2500000000 : ℝ)|=(534124701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5242005943/10000000000 : ℝ)|^4297 ≤ (42829076443529/100000000000000 : ℝ)^3273
        have hw : |(5242005943/10000000000 : ℝ)|=(5242005943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s4_2 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349760871/10000000000 : ℝ)*x 0 + (655250703/1250000000 : ℝ)*x 1 + (-267062361/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349760871/10000000000 : ℝ)^4297 ≤ (43988615746503/100000000000000 : ℝ)^3273 := by
    have hnat : (5349760871 : ℕ)^4297*100000000000000^3273 ≤ 43988615746503^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349760871 10000000000 43988615746503 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655250703/1250000000 : ℝ)^4297 ≤ (8565814604351/20000000000000 : ℝ)^3273 := by
    have hnat : (655250703 : ℕ)^4297*20000000000000^3273 ≤ 8565814604351^3273*1250000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655250703 1250000000 8565814604351 20000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (267062361/1250000000 : ℝ)^4297 ≤ (527292448719/4000000000000 : ℝ)^3273 := by
    have hnat : (267062361 : ℕ)^4297*4000000000000^3273 ≤ 527292448719^3273*1250000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267062361 1250000000 527292448719 4000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349760871/10000000000 : ℝ), (655250703/1250000000 : ℝ), (-267062361/1250000000 : ℝ)] ![(43988615746503/100000000000000 : ℝ), (8565814604351/20000000000000 : ℝ), (527292448719/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349760871/10000000000 : ℝ)|^4297 ≤ (43988615746503/100000000000000 : ℝ)^3273
        have hw : |(5349760871/10000000000 : ℝ)|=(5349760871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655250703/1250000000 : ℝ)|^4297 ≤ (8565814604351/20000000000000 : ℝ)^3273
        have hw : |(655250703/1250000000 : ℝ)|=(655250703/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-267062361/1250000000 : ℝ)|^4297 ≤ (527292448719/4000000000000 : ℝ)^3273
        have hw : |(-267062361/1250000000 : ℝ)|=(267062361/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s4_3 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (86554893/200000000 : ℝ)*x 0 + (4149830839/10000000000 : ℝ)*x 1 + (4512785109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86554893/200000000 : ℝ)^4297 ≤ (16650658775797/50000000000000 : ℝ)^3273 := by
    have hnat : (86554893 : ℕ)^4297*50000000000000^3273 ≤ 16650658775797^3273*200000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86554893 200000000 16650658775797 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4149830839/10000000000 : ℝ)^4297 ≤ (15757826379969/50000000000000 : ℝ)^3273 := by
    have hnat : (4149830839 : ℕ)^4297*50000000000000^3273 ≤ 15757826379969^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4149830839 10000000000 15757826379969 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4512785109/10000000000 : ℝ)^4297 ≤ (7036605934333/20000000000000 : ℝ)^3273 := by
    have hnat : (4512785109 : ℕ)^4297*20000000000000^3273 ≤ 7036605934333^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512785109 10000000000 7036605934333 20000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86554893/200000000 : ℝ), (4149830839/10000000000 : ℝ), (4512785109/10000000000 : ℝ)] ![(16650658775797/50000000000000 : ℝ), (15757826379969/50000000000000 : ℝ), (7036605934333/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86554893/200000000 : ℝ)|^4297 ≤ (16650658775797/50000000000000 : ℝ)^3273
        have hw : |(86554893/200000000 : ℝ)|=(86554893/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4149830839/10000000000 : ℝ)|^4297 ≤ (15757826379969/50000000000000 : ℝ)^3273
        have hw : |(4149830839/10000000000 : ℝ)|=(4149830839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4512785109/10000000000 : ℝ)|^4297 ≤ (7036605934333/20000000000000 : ℝ)^3273
        have hw : |(4512785109/10000000000 : ℝ)|=(4512785109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s4_4 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1024001503/5000000000 : ℝ)*x 0 + (1310661499/2500000000 : ℝ)*x 1 + (5414971917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1024001503/5000000000 : ℝ)^4297 ≤ (12470145996363/100000000000000 : ℝ)^3273 := by
    have hnat : (1024001503 : ℕ)^4297*100000000000000^3273 ≤ 12470145996363^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024001503 5000000000 12470145996363 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310661499/2500000000 : ℝ)^4297 ≤ (5354492767859/12500000000000 : ℝ)^3273 := by
    have hnat : (1310661499 : ℕ)^4297*12500000000000^3273 ≤ 5354492767859^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310661499 2500000000 5354492767859 12500000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414971917/10000000000 : ℝ)^4297 ≤ (44693911841801/100000000000000 : ℝ)^3273 := by
    have hnat : (5414971917 : ℕ)^4297*100000000000000^3273 ≤ 44693911841801^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414971917 10000000000 44693911841801 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1024001503/5000000000 : ℝ), (1310661499/2500000000 : ℝ), (5414971917/10000000000 : ℝ)] ![(12470145996363/100000000000000 : ℝ), (5354492767859/12500000000000 : ℝ), (44693911841801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1024001503/5000000000 : ℝ)|^4297 ≤ (12470145996363/100000000000000 : ℝ)^3273
        have hw : |(-1024001503/5000000000 : ℝ)|=(1024001503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310661499/2500000000 : ℝ)|^4297 ≤ (5354492767859/12500000000000 : ℝ)^3273
        have hw : |(1310661499/2500000000 : ℝ)|=(1310661499/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414971917/10000000000 : ℝ)|^4297 ≤ (44693911841801/100000000000000 : ℝ)^3273
        have hw : |(5414971917/10000000000 : ℝ)|=(5414971917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s4_5 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326267143/2500000000 : ℝ)*x 0 + (-245441557/1250000000 : ℝ)*x 1 + (5414972279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326267143/2500000000 : ℝ)^4297 ≤ (21753395581853/50000000000000 : ℝ)^3273 := by
    have hnat : (1326267143 : ℕ)^4297*50000000000000^3273 ≤ 21753395581853^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326267143 2500000000 21753395581853 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (245441557/1250000000 : ℝ)^4297 ≤ (2949823264779/25000000000000 : ℝ)^3273 := by
    have hnat : (245441557 : ℕ)^4297*25000000000000^3273 ≤ 2949823264779^3273*1250000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245441557 1250000000 2949823264779 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414972279/10000000000 : ℝ)^4297 ≤ (5586739470557/12500000000000 : ℝ)^3273 := by
    have hnat : (5414972279 : ℕ)^4297*12500000000000^3273 ≤ 5586739470557^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414972279 10000000000 5586739470557 12500000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326267143/2500000000 : ℝ), (-245441557/1250000000 : ℝ), (5414972279/10000000000 : ℝ)] ![(21753395581853/50000000000000 : ℝ), (2949823264779/25000000000000 : ℝ), (5586739470557/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326267143/2500000000 : ℝ)|^4297 ≤ (21753395581853/50000000000000 : ℝ)^3273
        have hw : |(1326267143/2500000000 : ℝ)|=(1326267143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-245441557/1250000000 : ℝ)|^4297 ≤ (2949823264779/25000000000000 : ℝ)^3273
        have hw : |(-245441557/1250000000 : ℝ)|=(245441557/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414972279/10000000000 : ℝ)|^4297 ≤ (5586739470557/12500000000000 : ℝ)^3273
        have hw : |(5414972279/10000000000 : ℝ)|=(5414972279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s4_6 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652534153/5000000000 : ℝ)*x 0 + (2707486157/5000000000 : ℝ)*x 1 + (-1963532771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652534153/5000000000 : ℝ)^4297 ≤ (8701357659949/20000000000000 : ℝ)^3273 := by
    have hnat : (2652534153 : ℕ)^4297*20000000000000^3273 ≤ 8701357659949^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652534153 5000000000 8701357659949 20000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707486157/5000000000 : ℝ)^4297 ≤ (22346958071859/50000000000000 : ℝ)^3273 := by
    have hnat : (2707486157 : ℕ)^4297*50000000000000^3273 ≤ 22346958071859^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707486157 5000000000 22346958071859 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1963532771/10000000000 : ℝ)^4297 ≤ (11799295544239/100000000000000 : ℝ)^3273 := by
    have hnat : (1963532771 : ℕ)^4297*100000000000000^3273 ≤ 11799295544239^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1963532771 10000000000 11799295544239 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652534153/5000000000 : ℝ), (2707486157/5000000000 : ℝ), (-1963532771/10000000000 : ℝ)] ![(8701357659949/20000000000000 : ℝ), (22346958071859/50000000000000 : ℝ), (11799295544239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652534153/5000000000 : ℝ)|^4297 ≤ (8701357659949/20000000000000 : ℝ)^3273
        have hw : |(2652534153/5000000000 : ℝ)|=(2652534153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707486157/5000000000 : ℝ)|^4297 ≤ (22346958071859/50000000000000 : ℝ)^3273
        have hw : |(2707486157/5000000000 : ℝ)|=(2707486157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1963532771/10000000000 : ℝ)|^4297 ≤ (11799295544239/100000000000000 : ℝ)^3273
        have hw : |(-1963532771/10000000000 : ℝ)|=(1963532771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s4_7 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4327772323/10000000000 : ℝ)*x 0 + (902289407/2000000000 : ℝ)*x 1 + (1037794077/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4327772323/10000000000 : ℝ)^4297 ≤ (16650798556049/50000000000000 : ℝ)^3273 := by
    have hnat : (4327772323 : ℕ)^4297*50000000000000^3273 ≤ 16650798556049^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4327772323 10000000000 16650798556049 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (902289407/2000000000 : ℝ)^4297 ≤ (8792333621569/25000000000000 : ℝ)^3273 := by
    have hnat : (902289407 : ℕ)^4297*25000000000000^3273 ≤ 8792333621569^3273*2000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902289407 2000000000 8792333621569 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1037794077/2500000000 : ℝ)^4297 ≤ (6305813677431/20000000000000 : ℝ)^3273 := by
    have hnat : (1037794077 : ℕ)^4297*20000000000000^3273 ≤ 6305813677431^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037794077 2500000000 6305813677431 20000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4327772323/10000000000 : ℝ), (902289407/2000000000 : ℝ), (1037794077/2500000000 : ℝ)] ![(16650798556049/50000000000000 : ℝ), (8792333621569/25000000000000 : ℝ), (6305813677431/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4327772323/10000000000 : ℝ)|^4297 ≤ (16650798556049/50000000000000 : ℝ)^3273
        have hw : |(4327772323/10000000000 : ℝ)|=(4327772323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(902289407/2000000000 : ℝ)|^4297 ≤ (8792333621569/25000000000000 : ℝ)^3273
        have hw : |(902289407/2000000000 : ℝ)|=(902289407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1037794077/2500000000 : ℝ)|^4297 ≤ (6305813677431/20000000000000 : ℝ)^3273
        have hw : |(1037794077/2500000000 : ℝ)|=(1037794077/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1337_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154531637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7507/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2169/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2217/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (369/2500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7507/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2169/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7507/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2169/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7507/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2169/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7507/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2169/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7507/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2169/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7507/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2169/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2169/20000 : ℝ) ^ (537/128 : ℝ) ≤ (4481841590647191/50000000000000000000 : ℝ) := by
    have hpowers : (2169/20000 : ℝ)^537 ≤ (4481841590647191/50000000000000000000 : ℝ)^128 := by
      have hnat : (2169 : ℕ)^537*50000000000000000000^128 ≤ 4481841590647191^128*20000^537 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2169 20000 4481841590647191 50000000000000000000 537 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2169/20000 : ℝ)) (X := (4481841590647191/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hpowhi : (7507/50000 : ℝ) ^ (537/128 : ℝ) ≤ (35086908273080859/100000000000000000000 : ℝ) := by
    have hpowers : (7507/50000 : ℝ)^537 ≤ (35086908273080859/100000000000000000000 : ℝ)^128 := by
      have hnat : (7507 : ℕ)^537*100000000000000000000^128 ≤ 35086908273080859^128*50000^537 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7507 50000 35086908273080859 100000000000000000000 537 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7507/50000 : ℝ)) (X := (35086908273080859/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004481841590647191/25000000000000000000 : ℝ) ≤ (5000213644902189/5000000000000000 : ℝ) ^ (537/128 : ℝ) := by
    have hpowers : (25004481841590647191/25000000000000000000 : ℝ)^128 ≤ (5000213644902189/5000000000000000 : ℝ)^537 := by
      have hnat : (25004481841590647191 : ℕ)^128*5000000000000000^537 ≤ 5000213644902189^537*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004481841590647191 25000000000000000000 5000213644902189 5000000000000000 128 537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000213644902189/5000000000000000 : ℝ)) (X := (25004481841590647191/25000000000000000000 : ℝ)) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100044050591454375241/100000000000000000000 : ℝ) ≤ (10001049819381473/10000000000000000 : ℝ) ^ (537/128 : ℝ) := by
    have hpowers : (100044050591454375241/100000000000000000000 : ℝ)^128 ≤ (10001049819381473/10000000000000000 : ℝ)^537 := by
      have hnat : (100044050591454375241 : ℕ)^128*10000000000000000^537 ≤ 10001049819381473^537*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100044050591454375241 100000000000000000000 10001049819381473 10000000000000000 128 537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001049819381473/10000000000000000 : ℝ)) (X := (100044050591454375241/100000000000000000000 : ℝ)) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035086908273080859/50000000000000000000 : ℝ) ≤ (1250209043619821/1250000000000000 : ℝ) ^ (537/128 : ℝ) := by
    have hpowers : (50035086908273080859/50000000000000000000 : ℝ)^128 ≤ (1250209043619821/1250000000000000 : ℝ)^537 := by
      have hnat : (50035086908273080859 : ℕ)^128*1250000000000000^537 ≤ 1250209043619821^537*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035086908273080859 50000000000000000000 1250209043619821 1250000000000000 128 537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250209043619821/1250000000000000 : ℝ)) (X := (50035086908273080859/50000000000000000000 : ℝ)) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4481841590647191/50000000000000000000 : ℝ) ≤ ((10419569676166815333/10422500000000000000 : ℝ)+2*(124505915419/83380000000000 : ℝ)*(2169/20000 : ℝ))^(537/128 : ℝ) := by
    rw [show (10419569676166815333/10422500000000000000 : ℝ)+2*(124505915419/83380000000000 : ℝ)*(2169/20000 : ℝ)=(5000213644902189/5000000000000000 : ℝ) by norm_num, show 1+2*(4481841590647191/50000000000000000000 : ℝ)=(25004481841590647191/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35086908273080859/100000000000000000000 : ℝ)+(4481841590647191/50000000000000000000 : ℝ) ≤ ((10419569676166815333/10422500000000000000 : ℝ)+(124505915419/83380000000000 : ℝ)*((7507/50000 : ℝ)+(2169/20000 : ℝ)))^(537/128 : ℝ) := by
    rw [show (10419569676166815333/10422500000000000000 : ℝ)+(124505915419/83380000000000 : ℝ)*((7507/50000 : ℝ)+(2169/20000 : ℝ))=(10001049819381473/10000000000000000 : ℝ) by norm_num, show 1+(35086908273080859/100000000000000000000 : ℝ)+(4481841590647191/50000000000000000000 : ℝ)=(100044050591454375241/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35086908273080859/100000000000000000000 : ℝ) ≤ ((10419569676166815333/10422500000000000000 : ℝ)+2*(124505915419/83380000000000 : ℝ)*(7507/50000 : ℝ))^(537/128 : ℝ) := by
    rw [show (10419569676166815333/10422500000000000000 : ℝ)+2*(124505915419/83380000000000 : ℝ)*(7507/50000 : ℝ)=(1250209043619821/1250000000000000 : ℝ) by norm_num, show 1+2*(35086908273080859/100000000000000000000 : ℝ)=(50035086908273080859/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10419569676166815333/10422500000000000000 : ℝ)*(X 1 0+X 2 0)+(124505915419/83380000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (537/128 : ℝ)) (lo := (2169/20000 : ℝ)) (hi := (7507/50000 : ℝ)) (c := (10419569676166815333/10422500000000000000 : ℝ)) (alpha := (124505915419/83380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10419569676166815333/10422500000000000000 : ℝ)*(X 0 1+X 2 1)+(124505915419/83380000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (537/128 : ℝ)) (lo := (2169/20000 : ℝ)) (hi := (7507/50000 : ℝ)) (c := (10419569676166815333/10422500000000000000 : ℝ)) (alpha := (124505915419/83380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10419569676166815333/10422500000000000000 : ℝ)*(X 0 2+X 1 2)+(124505915419/83380000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (537/128 : ℝ)) (lo := (2169/20000 : ℝ)) (hi := (7507/50000 : ℝ)) (c := (10419569676166815333/10422500000000000000 : ℝ)) (alpha := (124505915419/83380000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-20479893/100000000 : ℝ)*X 0 0+(5415615457/10000000000 : ℝ)*X 0 1+(2621003051/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349760617/10000000000 : ℝ)*X 1 0+(-534124701/2500000000 : ℝ)*X 1 1+(5242005943/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349760871/10000000000 : ℝ)*X 2 0+(655250703/1250000000 : ℝ)*X 2 1+(-267062361/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((86554893/200000000 : ℝ)*X 0 0+(4149830839/10000000000 : ℝ)*X 0 1+(4512785109/10000000000 : ℝ)*X 0 2+(86554893/200000000 : ℝ)*X 1 0+(4149830839/10000000000 : ℝ)*X 1 1+(4512785109/10000000000 : ℝ)*X 1 2+(86554893/200000000 : ℝ)*X 2 0+(4149830839/10000000000 : ℝ)*X 2 1+(4512785109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1024001503/5000000000 : ℝ)*X 0 0+(1310661499/2500000000 : ℝ)*X 0 1+(5414971917/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326267143/2500000000 : ℝ)*X 1 0+(-245441557/1250000000 : ℝ)*X 1 1+(5414972279/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652534153/5000000000 : ℝ)*X 2 0+(2707486157/5000000000 : ℝ)*X 2 1+(-1963532771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4327772323/10000000000 : ℝ)*X 0 0+(902289407/2000000000 : ℝ)*X 0 1+(1037794077/2500000000 : ℝ)*X 0 2+(4327772323/10000000000 : ℝ)*X 1 0+(902289407/2000000000 : ℝ)*X 1 1+(1037794077/2500000000 : ℝ)*X 1 2+(4327772323/10000000000 : ℝ)*X 2 0+(902289407/2000000000 : ℝ)*X 2 1+(1037794077/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (195703829660491726133560731/65140625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (670879541/100000000000000 : ℝ)*(base19) + (942345989/100000000000000 : ℝ)*(base23) + (726547/625000000000 : ℝ)*(lower2) + (52775597/100000000000000 : ℝ)*(upper3) + (23033921/20000000000000 : ℝ)*(lower4) + (266101957963089/6250000000000 : ℝ)*(major0) + (266101957963089/6250000000000 : ℝ)*(major1) + (266101957963089/6250000000000 : ℝ)*(major2) + (2880034096927227/50000000000000 : ℝ)*(sp0) + (2880038815759151/50000000000000 : ℝ)*(sp1) + (2880038680025927/50000000000000 : ℝ)*(sp2) + (2755175246921767/100000000000000 : ℝ)*(sp3) + (10108543389/100000000000000 : ℝ)*(sp4) + (1125669369/12500000000000 : ℝ)*(sp7) + (2755184252276719/100000000000000 : ℝ)*(f.failure) + (5760078302397843/100000000000000 : ℝ)*(f.sum) + (49095212867/260562500000000000000000000 : ℝ)*base66 + (260828553500785881/32570312500000000000000000000000 : ℝ)*base67 + (553453934183368637/65140625000000000000000000000000 : ℝ)*base69 + (61074419242568863/65140625000000000000000000000000 : ℝ)*base72 + (2315343303431/4169000000000000000000000000 : ℝ)*base73 + (42975800530176939/8142578125000000000000000000000 : ℝ)*base75 + (778855802124618637/65140625000000000000000000000000 : ℝ)*base77 + (59153511318338253/16285156250000000000000000000000 : ℝ)*base79 + (12853418647733/4169000000000000000000000000 : ℝ)*base81 + (35940997/10000000000000000000000 : ℝ)*base90 + (35940997/10000000000000000000000 : ℝ)*base92 + (35940997/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1192033844703139525124725239/104225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2180329089/100000000000000 : ℝ)*(base19) + (1858873561/100000000000000 : ℝ)*(base23) + (4958163/1562500000000 : ℝ)*(upper3) + (3637923/20000000000000 : ℝ)*(lower4) + (11820803/6250000000000 : ℝ)*(upper5) + (857864095219239/20000000000000 : ℝ)*(major0) + (857864095219239/20000000000000 : ℝ)*(major1) + (857864095219239/20000000000000 : ℝ)*(major2) + (6449457899/12500000000000 : ℝ)*(sp1) + (43905738343/100000000000000 : ℝ)*(sp2) + (5802949741965643/100000000000000 : ℝ)*(sp4) + (2901447982986681/50000000000000 : ℝ)*(sp5) + (290145198867687/5000000000000 : ℝ)*(sp6) + (2775690828989403/100000000000000 : ℝ)*(sp7) + (2775690828989403/100000000000000 : ℝ)*(f.failure) + (5802949741965643/100000000000000 : ℝ)*(f.sum) + (6210208747927/2084500000000000000000000000 : ℝ)*base66 + (1805853488975566587/208450000000000000000000000000000 : ℝ)*base67 + (1481679462000333413/208450000000000000000000000000000 : ℝ)*base70 + (803689223589766587/208450000000000000000000000000000 : ℝ)*base71 + (8426310847/1628515625000000000000000 : ℝ)*base73 + (1697405157525316587/208450000000000000000000000000000 : ℝ)*base75 + (620909285570516587/208450000000000000000000000000000 : ℝ)*base77 + (3096740419520233413/208450000000000000000000000000000 : ℝ)*base80 + (1798547888259/833800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1242711/10000000000000000000000 : ℝ)*base89 + (1242711/10000000000000000000000 : ℝ)*base91 + (1242711/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1337_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154531637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7507/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2169/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2217/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (369/2500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1337_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1337_s5_0 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-512061649/2500000000 : ℝ)*x 0 + (5413371411/10000000000 : ℝ)*x 1 + (5244081111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (512061649/2500000000 : ℝ)^4297 ≤ (12472093273803/100000000000000 : ℝ)^3273 := by
    have hnat : (512061649 : ℕ)^4297*100000000000000^3273 ≤ 12472093273803^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512061649 2500000000 12472093273803 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413371411/10000000000 : ℝ)^4297 ≤ (22338284730219/50000000000000 : ℝ)^3273 := by
    have hnat : (5413371411 : ℕ)^4297*50000000000000^3273 ≤ 22338284730219^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413371411 10000000000 22338284730219 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244081111/10000000000 : ℝ)^4297 ≤ (5356417155019/12500000000000 : ℝ)^3273 := by
    have hnat : (5244081111 : ℕ)^4297*12500000000000^3273 ≤ 5356417155019^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244081111 10000000000 5356417155019 12500000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-512061649/2500000000 : ℝ), (5413371411/10000000000 : ℝ), (5244081111/10000000000 : ℝ)] ![(12472093273803/100000000000000 : ℝ), (22338284730219/50000000000000 : ℝ), (5356417155019/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-512061649/2500000000 : ℝ)|^4297 ≤ (12472093273803/100000000000000 : ℝ)^3273
        have hw : |(-512061649/2500000000 : ℝ)|=(512061649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413371411/10000000000 : ℝ)|^4297 ≤ (22338284730219/50000000000000 : ℝ)^3273
        have hw : |(5413371411/10000000000 : ℝ)|=(5413371411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244081111/10000000000 : ℝ)|^4297 ≤ (5356417155019/12500000000000 : ℝ)^3273
        have hw : |(5244081111/10000000000 : ℝ)|=(5244081111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s5_1 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349188621/10000000000 : ℝ)*x 0 + (-1067256337/5000000000 : ℝ)*x 1 + (655510139/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349188621/10000000000 : ℝ)^4297 ≤ (43982438373751/100000000000000 : ℝ)^3273 := by
    have hnat : (5349188621 : ℕ)^4297*100000000000000^3273 ≤ 43982438373751^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349188621 10000000000 43982438373751 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1067256337/5000000000 : ℝ)^4297 ≤ (526648974589/4000000000000 : ℝ)^3273 := by
    have hnat : (1067256337 : ℕ)^4297*4000000000000^3273 ≤ 526648974589^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067256337 5000000000 526648974589 4000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655510139/1250000000 : ℝ)^4297 ≤ (133910428909/312500000000 : ℝ)^3273 := by
    have hnat : (655510139 : ℕ)^4297*312500000000^3273 ≤ 133910428909^3273*1250000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655510139 1250000000 133910428909 312500000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349188621/10000000000 : ℝ), (-1067256337/5000000000 : ℝ), (655510139/1250000000 : ℝ)] ![(43982438373751/100000000000000 : ℝ), (526648974589/4000000000000 : ℝ), (133910428909/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349188621/10000000000 : ℝ)|^4297 ≤ (43982438373751/100000000000000 : ℝ)^3273
        have hw : |(5349188621/10000000000 : ℝ)|=(5349188621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1067256337/5000000000 : ℝ)|^4297 ≤ (526648974589/4000000000000 : ℝ)^3273
        have hw : |(-1067256337/5000000000 : ℝ)|=(1067256337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655510139/1250000000 : ℝ)|^4297 ≤ (133910428909/312500000000 : ℝ)^3273
        have hw : |(655510139/1250000000 : ℝ)|=(655510139/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s5_2 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337297159/2500000000 : ℝ)*x 0 + (655510139/1250000000 : ℝ)*x 1 + (-1067256327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337297159/2500000000 : ℝ)^4297 ≤ (5497804816959/12500000000000 : ℝ)^3273 := by
    have hnat : (1337297159 : ℕ)^4297*12500000000000^3273 ≤ 5497804816959^3273*2500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337297159 2500000000 5497804816959 12500000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655510139/1250000000 : ℝ)^4297 ≤ (133910428909/312500000000 : ℝ)^3273 := by
    have hnat : (655510139 : ℕ)^4297*312500000000^3273 ≤ 133910428909^3273*1250000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655510139 1250000000 133910428909 312500000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1067256327/5000000000 : ℝ)^4297 ≤ (3291556050691/25000000000000 : ℝ)^3273 := by
    have hnat : (1067256327 : ℕ)^4297*25000000000000^3273 ≤ 3291556050691^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067256327 5000000000 3291556050691 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337297159/2500000000 : ℝ), (655510139/1250000000 : ℝ), (-1067256327/5000000000 : ℝ)] ![(5497804816959/12500000000000 : ℝ), (133910428909/312500000000 : ℝ), (3291556050691/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337297159/2500000000 : ℝ)|^4297 ≤ (5497804816959/12500000000000 : ℝ)^3273
        have hw : |(1337297159/2500000000 : ℝ)|=(1337297159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655510139/1250000000 : ℝ)|^4297 ≤ (133910428909/312500000000 : ℝ)^3273
        have hw : |(655510139/1250000000 : ℝ)|=(655510139/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1067256327/5000000000 : ℝ)|^4297 ≤ (3291556050691/25000000000000 : ℝ)^3273
        have hw : |(-1067256327/5000000000 : ℝ)|=(1067256327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s5_3 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (270493753/625000000 : ℝ)*x 0 + (64911357/156250000 : ℝ)*x 1 + (4508250677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270493753/625000000 : ℝ)^4297 ≤ (33302887433563/100000000000000 : ℝ)^3273 := by
    have hnat : (270493753 : ℕ)^4297*100000000000000^3273 ≤ 33302887433563^3273*625000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270493753 625000000 33302887433563 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (64911357/156250000 : ℝ)^4297 ≤ (31560487640113/100000000000000 : ℝ)^3273 := by
    have hnat : (64911357 : ℕ)^4297*100000000000000^3273 ≤ 31560487640113^3273*156250000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      64911357 156250000 31560487640113 100000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4508250677/10000000000 : ℝ)^4297 ≤ (7027324982171/20000000000000 : ℝ)^3273 := by
    have hnat : (4508250677 : ℕ)^4297*20000000000000^3273 ≤ 7027324982171^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508250677 10000000000 7027324982171 20000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270493753/625000000 : ℝ), (64911357/156250000 : ℝ), (4508250677/10000000000 : ℝ)] ![(33302887433563/100000000000000 : ℝ), (31560487640113/100000000000000 : ℝ), (7027324982171/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270493753/625000000 : ℝ)|^4297 ≤ (33302887433563/100000000000000 : ℝ)^3273
        have hw : |(270493753/625000000 : ℝ)|=(270493753/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(64911357/156250000 : ℝ)|^4297 ≤ (31560487640113/100000000000000 : ℝ)^3273
        have hw : |(64911357/156250000 : ℝ)|=(64911357/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4508250677/10000000000 : ℝ)|^4297 ≤ (7027324982171/20000000000000 : ℝ)^3273
        have hw : |(4508250677/10000000000 : ℝ)|=(4508250677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s5_4 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2048259/10000000 : ℝ)*x 0 + (5244689743/10000000000 : ℝ)*x 1 + (5412759627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2048259/10000000 : ℝ)^4297 ≤ (3118048108571/25000000000000 : ℝ)^3273 := by
    have hnat : (2048259 : ℕ)^4297*25000000000000^3273 ≤ 3118048108571^3273*10000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2048259 10000000 3118048108571 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244689743/10000000000 : ℝ)^4297 ≤ (5357233337009/12500000000000 : ℝ)^3273 := by
    have hnat : (5244689743 : ℕ)^4297*12500000000000^3273 ≤ 5357233337009^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244689743 10000000000 5357233337009 12500000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412759627/10000000000 : ℝ)^4297 ≤ (22334970430483/50000000000000 : ℝ)^3273 := by
    have hnat : (5412759627 : ℕ)^4297*50000000000000^3273 ≤ 22334970430483^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412759627 10000000000 22334970430483 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2048259/10000000 : ℝ), (5244689743/10000000000 : ℝ), (5412759627/10000000000 : ℝ)] ![(3118048108571/25000000000000 : ℝ), (5357233337009/12500000000000 : ℝ), (22334970430483/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2048259/10000000 : ℝ)|^4297 ≤ (3118048108571/25000000000000 : ℝ)^3273
        have hw : |(-2048259/10000000 : ℝ)|=(2048259/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244689743/10000000000 : ℝ)|^4297 ≤ (5357233337009/12500000000000 : ℝ)^3273
        have hw : |(5244689743/10000000000 : ℝ)|=(5244689743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412759627/10000000000 : ℝ)|^4297 ≤ (22334970430483/50000000000000 : ℝ)^3273
        have hw : |(5412759627/10000000000 : ℝ)|=(5412759627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s5_5 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652804231/5000000000 : ℝ)*x 0 + (-982917067/5000000000 : ℝ)*x 1 + (5412759629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652804231/5000000000 : ℝ)^4297 ≤ (2719537757951/6250000000000 : ℝ)^3273 := by
    have hnat : (2652804231 : ℕ)^4297*6250000000000^3273 ≤ 2719537757951^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652804231 5000000000 2719537757951 6250000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (982917067/5000000000 : ℝ)^4297 ≤ (5908727482627/50000000000000 : ℝ)^3273 := by
    have hnat : (982917067 : ℕ)^4297*50000000000000^3273 ≤ 5908727482627^3273*5000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982917067 5000000000 5908727482627 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412759629/10000000000 : ℝ)^4297 ≤ (11167485220659/25000000000000 : ℝ)^3273 := by
    have hnat : (5412759629 : ℕ)^4297*25000000000000^3273 ≤ 11167485220659^3273*10000000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412759629 10000000000 11167485220659 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652804231/5000000000 : ℝ), (-982917067/5000000000 : ℝ), (5412759629/10000000000 : ℝ)] ![(2719537757951/6250000000000 : ℝ), (5908727482627/50000000000000 : ℝ), (11167485220659/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652804231/5000000000 : ℝ)|^4297 ≤ (2719537757951/6250000000000 : ℝ)^3273
        have hw : |(2652804231/5000000000 : ℝ)|=(2652804231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-982917067/5000000000 : ℝ)|^4297 ≤ (5908727482627/50000000000000 : ℝ)^3273
        have hw : |(-982917067/5000000000 : ℝ)|=(982917067/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412759629/10000000000 : ℝ)|^4297 ≤ (11167485220659/25000000000000 : ℝ)^3273
        have hw : |(5412759629/10000000000 : ℝ)|=(5412759629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s5_6 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132640211/250000000 : ℝ)*x 0 + (108255193/200000000 : ℝ)*x 1 + (-245729267/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132640211/250000000 : ℝ)^4297 ≤ (2175630194517/5000000000000 : ℝ)^3273 := by
    have hnat : (132640211 : ℕ)^4297*5000000000000^3273 ≤ 2175630194517^3273*250000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132640211 250000000 2175630194517 5000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108255193/200000000 : ℝ)^4297 ≤ (11167485277541/25000000000000 : ℝ)^3273 := by
    have hnat : (108255193 : ℕ)^4297*25000000000000^3273 ≤ 11167485277541^3273*200000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108255193 200000000 11167485277541 25000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (245729267/1250000000 : ℝ)^4297 ≤ (5908727490519/50000000000000 : ℝ)^3273 := by
    have hnat : (245729267 : ℕ)^4297*50000000000000^3273 ≤ 5908727490519^3273*1250000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      245729267 1250000000 5908727490519 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132640211/250000000 : ℝ), (108255193/200000000 : ℝ), (-245729267/1250000000 : ℝ)] ![(2175630194517/5000000000000 : ℝ), (11167485277541/25000000000000 : ℝ), (5908727490519/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132640211/250000000 : ℝ)|^4297 ≤ (2175630194517/5000000000000 : ℝ)^3273
        have hw : |(132640211/250000000 : ℝ)|=(132640211/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108255193/200000000 : ℝ)|^4297 ≤ (11167485277541/25000000000000 : ℝ)^3273
        have hw : |(108255193/200000000 : ℝ)|=(108255193/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-245729267/1250000000 : ℝ)|^4297 ≤ (5908727490519/50000000000000 : ℝ)^3273
        have hw : |(-245729267/1250000000 : ℝ)|=(245729267/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1337_s5_7 (p : ℝ) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (216396297/500000000 : ℝ)*x 0 + (563372287/1250000000 : ℝ)*x 1 + (83112117/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216396297/500000000 : ℝ)^4297 ≤ (1665157450241/5000000000000 : ℝ)^3273 := by
    have hnat : (216396297 : ℕ)^4297*5000000000000^3273 ≤ 1665157450241^3273*500000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216396297 500000000 1665157450241 5000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (563372287/1250000000 : ℝ)^4297 ≤ (17561803079731/50000000000000 : ℝ)^3273 := by
    have hnat : (563372287 : ℕ)^4297*50000000000000^3273 ≤ 17561803079731^3273*1250000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563372287 1250000000 17561803079731 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (83112117/200000000 : ℝ)^4297 ≤ (15786622407783/50000000000000 : ℝ)^3273 := by
    have hnat : (83112117 : ℕ)^4297*50000000000000^3273 ≤ 15786622407783^3273*200000000^4297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83112117 200000000 15786622407783 50000000000000 4297 3273 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4297/1024 : ℝ)) 4297 3273 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(216396297/500000000 : ℝ), (563372287/1250000000 : ℝ), (83112117/200000000 : ℝ)] ![(1665157450241/5000000000000 : ℝ), (17561803079731/50000000000000 : ℝ), (15786622407783/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(216396297/500000000 : ℝ)|^4297 ≤ (1665157450241/5000000000000 : ℝ)^3273
        have hw : |(216396297/500000000 : ℝ)|=(216396297/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(563372287/1250000000 : ℝ)|^4297 ≤ (17561803079731/50000000000000 : ℝ)^3273
        have hw : |(563372287/1250000000 : ℝ)|=(563372287/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(83112117/200000000 : ℝ)|^4297 ≤ (15786622407783/50000000000000 : ℝ)^3273
        have hw : |(83112117/200000000 : ℝ)|=(83112117/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1337_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154531637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (369/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2217/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11129/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14713/100000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (2217/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (369/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2217/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (369/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2217/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (369/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2217/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (369/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2217/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (369/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2217/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2217/20000 : ℝ) ^ (537/128 : ℝ) ≤ (9825795717180889/100000000000000000000 : ℝ) := by
    have hpowers : (2217/20000 : ℝ)^537 ≤ (9825795717180889/100000000000000000000 : ℝ)^128 := by
      have hnat : (2217 : ℕ)^537*100000000000000000000^128 ≤ 9825795717180889^128*20000^537 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2217 20000 9825795717180889 100000000000000000000 537 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2217/20000 : ℝ)) (X := (9825795717180889/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hpowhi : (369/2500 : ℝ) ^ (537/128 : ℝ) ≤ (32663115690799873/100000000000000000000 : ℝ) := by
    have hpowers : (369/2500 : ℝ)^537 ≤ (32663115690799873/100000000000000000000 : ℝ)^128 := by
      have hnat : (369 : ℕ)^537*100000000000000000000^128 ≤ 32663115690799873^128*2500^537 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        369 2500 32663115690799873 100000000000000000000 537 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (369/2500 : ℝ)) (X := (32663115690799873/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009825795717180889/50000000000000000000 : ℝ) ≤ (10000468382770929/10000000000000000 : ℝ) ^ (537/128 : ℝ) := by
    have hpowers : (50009825795717180889/50000000000000000000 : ℝ)^128 ≤ (10000468382770929/10000000000000000 : ℝ)^537 := by
      have hnat : (50009825795717180889 : ℕ)^128*10000000000000000^537 ≤ 10000468382770929^537*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009825795717180889 50000000000000000000 10000468382770929 10000000000000000 128 537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000468382770929/10000000000000000 : ℝ)) (X := (50009825795717180889/50000000000000000000 : ℝ)) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50021244455703990381/50000000000000000000 : ℝ) ≤ (5000506303620551/5000000000000000 : ℝ) ^ (537/128 : ℝ) := by
    have hpowers : (50021244455703990381/50000000000000000000 : ℝ)^128 ≤ (5000506303620551/5000000000000000 : ℝ)^537 := by
      have hnat : (50021244455703990381 : ℕ)^128*5000000000000000^537 ≤ 5000506303620551^537*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021244455703990381 50000000000000000000 5000506303620551 5000000000000000 128 537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000506303620551/5000000000000000 : ℝ)) (X := (50021244455703990381/50000000000000000000 : ℝ)) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032663115690799873/50000000000000000000 : ℝ) ≤ (400062273268451/400000000000000 : ℝ) ^ (537/128 : ℝ) := by
    have hpowers : (50032663115690799873/50000000000000000000 : ℝ)^128 ≤ (400062273268451/400000000000000 : ℝ)^537 := by
      have hnat : (50032663115690799873 : ℕ)^128*400000000000000^537 ≤ 400062273268451^537*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032663115690799873 50000000000000000000 400062273268451 400000000000000 128 537 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400062273268451/400000000000000 : ℝ)) (X := (50032663115690799873/50000000000000000000 : ℝ)) (by norm_num) 537 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9825795717180889/100000000000000000000 : ℝ) ≤ ((2449310390011961911/2450000000000000000 : ℝ)+2*(544224470173/367500000000000 : ℝ)*(2217/20000 : ℝ))^(537/128 : ℝ) := by
    rw [show (2449310390011961911/2450000000000000000 : ℝ)+2*(544224470173/367500000000000 : ℝ)*(2217/20000 : ℝ)=(10000468382770929/10000000000000000 : ℝ) by norm_num, show 1+2*(9825795717180889/100000000000000000000 : ℝ)=(50009825795717180889/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32663115690799873/100000000000000000000 : ℝ)+(9825795717180889/100000000000000000000 : ℝ) ≤ ((2449310390011961911/2450000000000000000 : ℝ)+(544224470173/367500000000000 : ℝ)*((369/2500 : ℝ)+(2217/20000 : ℝ)))^(537/128 : ℝ) := by
    rw [show (2449310390011961911/2450000000000000000 : ℝ)+(544224470173/367500000000000 : ℝ)*((369/2500 : ℝ)+(2217/20000 : ℝ))=(5000506303620551/5000000000000000 : ℝ) by norm_num, show 1+(32663115690799873/100000000000000000000 : ℝ)+(9825795717180889/100000000000000000000 : ℝ)=(50021244455703990381/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32663115690799873/100000000000000000000 : ℝ) ≤ ((2449310390011961911/2450000000000000000 : ℝ)+2*(544224470173/367500000000000 : ℝ)*(369/2500 : ℝ))^(537/128 : ℝ) := by
    rw [show (2449310390011961911/2450000000000000000 : ℝ)+2*(544224470173/367500000000000 : ℝ)*(369/2500 : ℝ)=(400062273268451/400000000000000 : ℝ) by norm_num, show 1+2*(32663115690799873/100000000000000000000 : ℝ)=(50032663115690799873/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2449310390011961911/2450000000000000000 : ℝ)*(X 1 0+X 2 0)+(544224470173/367500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (537/128 : ℝ)) (lo := (2217/20000 : ℝ)) (hi := (369/2500 : ℝ)) (c := (2449310390011961911/2450000000000000000 : ℝ)) (alpha := (544224470173/367500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2449310390011961911/2450000000000000000 : ℝ)*(X 0 1+X 2 1)+(544224470173/367500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (537/128 : ℝ)) (lo := (2217/20000 : ℝ)) (hi := (369/2500 : ℝ)) (c := (2449310390011961911/2450000000000000000 : ℝ)) (alpha := (544224470173/367500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2449310390011961911/2450000000000000000 : ℝ)*(X 0 2+X 1 2)+(544224470173/367500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (537/128 : ℝ)) (lo := (2217/20000 : ℝ)) (hi := (369/2500 : ℝ)) (c := (2449310390011961911/2450000000000000000 : ℝ)) (alpha := (544224470173/367500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-512061649/2500000000 : ℝ)*X 0 0+(5413371411/10000000000 : ℝ)*X 0 1+(5244081111/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349188621/10000000000 : ℝ)*X 1 0+(-1067256337/5000000000 : ℝ)*X 1 1+(655510139/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337297159/2500000000 : ℝ)*X 2 0+(655510139/1250000000 : ℝ)*X 2 1+(-1067256327/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((270493753/625000000 : ℝ)*X 0 0+(64911357/156250000 : ℝ)*X 0 1+(4508250677/10000000000 : ℝ)*X 0 2+(270493753/625000000 : ℝ)*X 1 0+(64911357/156250000 : ℝ)*X 1 1+(4508250677/10000000000 : ℝ)*X 1 2+(270493753/625000000 : ℝ)*X 2 0+(64911357/156250000 : ℝ)*X 2 1+(4508250677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2048259/10000000 : ℝ)*X 0 0+(5244689743/10000000000 : ℝ)*X 0 1+(5412759627/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652804231/5000000000 : ℝ)*X 1 0+(-982917067/5000000000 : ℝ)*X 1 1+(5412759629/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132640211/250000000 : ℝ)*X 2 0+(108255193/200000000 : ℝ)*X 2 1+(-245729267/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((216396297/500000000 : ℝ)*X 0 0+(563372287/1250000000 : ℝ)*X 0 1+(83112117/200000000 : ℝ)*X 0 2+(216396297/500000000 : ℝ)*X 1 0+(563372287/1250000000 : ℝ)*X 1 1+(83112117/200000000 : ℝ)*X 1 2+(216396297/500000000 : ℝ)*X 2 0+(563372287/1250000000 : ℝ)*X 2 1+(83112117/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1337_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (48412912305027701017849709/7656250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (302785219/25000000000000 : ℝ)*(base19) + (1145574733/100000000000000 : ℝ)*(base23) + (1098329/2500000000000 : ℝ)*(lower2) + (153675223/100000000000000 : ℝ)*(upper3) + (24049501/20000000000000 : ℝ)*(upper5) + (545784622279777/12500000000000 : ℝ)*(major0) + (545784622279777/12500000000000 : ℝ)*(major1) + (545784622279777/12500000000000 : ℝ)*(major2) + (2953519003842573/50000000000000 : ℝ)*(sp0) + (1181412373868741/20000000000000 : ℝ)*(sp1) + (738382741863731/12500000000000 : ℝ)*(sp2) + (706369551476769/25000000000000 : ℝ)*(sp3) + (5014559887/20000000000000 : ℝ)*(sp4) + (6229653731/50000000000000 : ℝ)*(sp7) + (1412745332607269/50000000000000 : ℝ)*(f.failure) + (5907063080484581/100000000000000 : ℝ)*(f.sum) + (1382862396773/1148437500000000000000000000 : ℝ)*base65 + (377212567621516541/91875000000000000000000000000000 : ℝ)*base67 + (358933697169016541/91875000000000000000000000000000 : ℝ)*base69 + (450581855087233459/91875000000000000000000000000000 : ℝ)*base72 + (33026334159941/9187500000000000000000000000 : ℝ)*base74 + (302310031342141541/91875000000000000000000000000000 : ℝ)*base75 + (1249608112141541/91875000000000000000000000000000 : ℝ)*base77 + (870293311087141541/91875000000000000000000000000000 : ℝ)*base79 + (7904064976079/2296875000000000000000000000 : ℝ)*base82 + (43330647/5000000000000000000000 : ℝ)*base90 + (43330647/5000000000000000000000 : ℝ)*base92 + (43330647/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (320505135632602401222986371/30625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (372371203/20000000000000 : ℝ)*(base19) + (246577541/12500000000000 : ℝ)*(base23) + (3469891/1562500000000 : ℝ)*(upper3) + (12155037/20000000000000 : ℝ)*(lower4) + (42389423/20000000000000 : ℝ)*(upper5) + (1099485886947713/25000000000000 : ℝ)*(major0) + (1099485886947713/25000000000000 : ℝ)*(major1) + (1099485886947713/25000000000000 : ℝ)*(major2) + (7507714399/20000000000000 : ℝ)*(sp1) + (10020348481/25000000000000 : ℝ)*(sp2) + (37186900725873/625000000000 : ℝ)*(sp4) + (594986471571167/10000000000000 : ℝ)*(sp5) + (1487465515531357/25000000000000 : ℝ)*(sp6) + (2845982630592887/100000000000000 : ℝ)*(sp7) + (2845982630592887/100000000000000 : ℝ)*(f.failure) + (37186900725873/625000000000 : ℝ)*(f.sum) + (1256927305861/287109375000000000000000000 : ℝ)*base66 + (1210065102070658629/183750000000000000000000000000000 : ℝ)*base67 + (168844713138158629/183750000000000000000000000000000 : ℝ)*base69 + (1330448878155591371/183750000000000000000000000000000 : ℝ)*base72 + (100032832824073/9187500000000000000000000000 : ℝ)*base73 + (1856564665675658629/183750000000000000000000000000000 : ℝ)*base75 + (133912895284341371/183750000000000000000000000000000 : ℝ)*base78 + (1403729986000658629/183750000000000000000000000000000 : ℝ)*base79 + (33616466031073/9187500000000000000000000000 : ℝ)*base81 + (91333981/10000000000000000000000 : ℝ)*base90 + (91333981/10000000000000000000000 : ℝ)*base92 + (91333981/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1337_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154531637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (369/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2217/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11129/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14713/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1337_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1337_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154531637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4031/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9819/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11129/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14713/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1337_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1337_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1337_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (537/128 : ℝ) ≤ p) (hpb : p ≤ (4297/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154531637/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4031/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9819/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11129/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14713/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1337_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
