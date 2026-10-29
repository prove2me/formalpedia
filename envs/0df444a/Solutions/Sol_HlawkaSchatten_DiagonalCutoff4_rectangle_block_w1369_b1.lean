-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1369_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:20:31.784663+00:00
-- url     : https://prove2.me/submissions/b8e2a18e-b9c6-4747-8ae2-8d8e9887c750

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
theorem support_rectangle_w1369_s3_0 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2019370851/10000000000 : ℝ)*x 0 + (5423843459/10000000000 : ℝ)*x 1 + (1308464653/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2019370851/10000000000 : ℝ)^4329 ≤ (12301234311807/100000000000000 : ℝ)^3305 := by
    have hnat : (2019370851 : ℕ)^4329*100000000000000^3305 ≤ 12301234311807^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2019370851 10000000000 12301234311807 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423843459/10000000000 : ℝ)^4329 ≤ (44873152069353/100000000000000 : ℝ)^3305 := by
    have hnat : (5423843459 : ℕ)^4329*100000000000000^3305 ≤ 44873152069353^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423843459 10000000000 44873152069353 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1308464653/2500000000 : ℝ)^4329 ≤ (21412806803557/50000000000000 : ℝ)^3305 := by
    have hnat : (1308464653 : ℕ)^4329*50000000000000^3305 ≤ 21412806803557^3305*2500000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308464653 2500000000 21412806803557 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2019370851/10000000000 : ℝ), (5423843459/10000000000 : ℝ), (1308464653/2500000000 : ℝ)] ![(12301234311807/100000000000000 : ℝ), (44873152069353/100000000000000 : ℝ), (21412806803557/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2019370851/10000000000 : ℝ)|^4329 ≤ (12301234311807/100000000000000 : ℝ)^3305
        have hw : |(-2019370851/10000000000 : ℝ)|=(2019370851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423843459/10000000000 : ℝ)|^4329 ≤ (44873152069353/100000000000000 : ℝ)^3305
        have hw : |(5423843459/10000000000 : ℝ)|=(5423843459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1308464653/2500000000 : ℝ)|^4329 ≤ (21412806803557/50000000000000 : ℝ)^3305
        have hw : |(1308464653/2500000000 : ℝ)|=(1308464653/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s3_1 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267586171/500000000 : ℝ)*x 0 + (-1058201723/5000000000 : ℝ)*x 1 + (5233858737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267586171/500000000 : ℝ)^4329 ≤ (44093226390833/100000000000000 : ℝ)^3305 := by
    have hnat : (267586171 : ℕ)^4329*100000000000000^3305 ≤ 44093226390833^3305*500000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267586171 500000000 44093226390833 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1058201723/5000000000 : ℝ)^4329 ≤ (13081158647871/100000000000000 : ℝ)^3305 := by
    have hnat : (1058201723 : ℕ)^4329*100000000000000^3305 ≤ 13081158647871^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058201723 5000000000 13081158647871 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5233858737/10000000000 : ℝ)^4329 ≤ (8565122989363/20000000000000 : ℝ)^3305 := by
    have hnat : (5233858737 : ℕ)^4329*20000000000000^3305 ≤ 8565122989363^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233858737 10000000000 8565122989363 20000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267586171/500000000 : ℝ), (-1058201723/5000000000 : ℝ), (5233858737/10000000000 : ℝ)] ![(44093226390833/100000000000000 : ℝ), (13081158647871/100000000000000 : ℝ), (8565122989363/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267586171/500000000 : ℝ)|^4329 ≤ (44093226390833/100000000000000 : ℝ)^3305
        have hw : |(267586171/500000000 : ℝ)|=(267586171/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1058201723/5000000000 : ℝ)|^4329 ≤ (13081158647871/100000000000000 : ℝ)^3305
        have hw : |(-1058201723/5000000000 : ℝ)|=(1058201723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5233858737/10000000000 : ℝ)|^4329 ≤ (8565122989363/20000000000000 : ℝ)^3305
        have hw : |(5233858737/10000000000 : ℝ)|=(5233858737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s3_2 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351723441/10000000000 : ℝ)*x 0 + (654232317/1250000000 : ℝ)*x 1 + (-529100921/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351723441/10000000000 : ℝ)^4329 ≤ (44093226617461/100000000000000 : ℝ)^3305 := by
    have hnat : (5351723441 : ℕ)^4329*100000000000000^3305 ≤ 44093226617461^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351723441 10000000000 44093226617461 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (654232317/1250000000 : ℝ)^4329 ≤ (167287549971/390625000000 : ℝ)^3305 := by
    have hnat : (654232317 : ℕ)^4329*390625000000^3305 ≤ 167287549971^3305*1250000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654232317 1250000000 167287549971 390625000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (529100921/2500000000 : ℝ)^4329 ≤ (13081160574689/100000000000000 : ℝ)^3305 := by
    have hnat : (529100921 : ℕ)^4329*100000000000000^3305 ≤ 13081160574689^3305*2500000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529100921 2500000000 13081160574689 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351723441/10000000000 : ℝ), (654232317/1250000000 : ℝ), (-529100921/2500000000 : ℝ)] ![(44093226617461/100000000000000 : ℝ), (167287549971/390625000000 : ℝ), (13081160574689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351723441/10000000000 : ℝ)|^4329 ≤ (44093226617461/100000000000000 : ℝ)^3305
        have hw : |(5351723441/10000000000 : ℝ)|=(5351723441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(654232317/1250000000 : ℝ)|^4329 ≤ (167287549971/390625000000 : ℝ)^3305
        have hw : |(654232317/1250000000 : ℝ)|=(654232317/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-529100921/2500000000 : ℝ)|^4329 ≤ (13081160574689/100000000000000 : ℝ)^3305
        have hw : |(-529100921/2500000000 : ℝ)|=(529100921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s3_3 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4318696807/10000000000 : ℝ)*x 0 + (4122021841/10000000000 : ℝ)*x 1 + (4524004991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4318696807/10000000000 : ℝ)^4329 ≤ (33294518610699/100000000000000 : ℝ)^3305 := by
    have hnat : (4318696807 : ℕ)^4329*100000000000000^3305 ≤ 33294518610699^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318696807 10000000000 33294518610699 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4122021841/10000000000 : ℝ)^4329 ≤ (31322652280631/100000000000000 : ℝ)^3305 := by
    have hnat : (4122021841 : ℕ)^4329*100000000000000^3305 ≤ 31322652280631^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4122021841 10000000000 31322652280631 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4524004991/10000000000 : ℝ)^4329 ≤ (4422853636717/12500000000000 : ℝ)^3305 := by
    have hnat : (4524004991 : ℕ)^4329*12500000000000^3305 ≤ 4422853636717^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524004991 10000000000 4422853636717 12500000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4318696807/10000000000 : ℝ), (4122021841/10000000000 : ℝ), (4524004991/10000000000 : ℝ)] ![(33294518610699/100000000000000 : ℝ), (31322652280631/100000000000000 : ℝ), (4422853636717/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4318696807/10000000000 : ℝ)|^4329 ≤ (33294518610699/100000000000000 : ℝ)^3305
        have hw : |(4318696807/10000000000 : ℝ)|=(4318696807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4122021841/10000000000 : ℝ)|^4329 ≤ (31322652280631/100000000000000 : ℝ)^3305
        have hw : |(4122021841/10000000000 : ℝ)|=(4122021841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4524004991/10000000000 : ℝ)|^4329 ≤ (4422853636717/12500000000000 : ℝ)^3305
        have hw : |(4524004991/10000000000 : ℝ)|=(4524004991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s3_4 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1009694377/5000000000 : ℝ)*x 0 + (523463847/1000000000 : ℝ)*x 1 + (5423058951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1009694377/5000000000 : ℝ)^4329 ≤ (192209018127/1562500000000 : ℝ)^3305 := by
    have hnat : (1009694377 : ℕ)^4329*1562500000000^3305 ≤ 192209018127^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009694377 5000000000 192209018127 1562500000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523463847/1000000000 : ℝ)^4329 ≤ (42833972009711/100000000000000 : ℝ)^3305 := by
    have hnat : (523463847 : ℕ)^4329*100000000000000^3305 ≤ 42833972009711^3305*1000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523463847 1000000000 42833972009711 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423058951/10000000000 : ℝ)^4329 ≤ (8972930162267/20000000000000 : ℝ)^3305 := by
    have hnat : (5423058951 : ℕ)^4329*20000000000000^3305 ≤ 8972930162267^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423058951 10000000000 8972930162267 20000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1009694377/5000000000 : ℝ), (523463847/1000000000 : ℝ), (5423058951/10000000000 : ℝ)] ![(192209018127/1562500000000 : ℝ), (42833972009711/100000000000000 : ℝ), (8972930162267/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1009694377/5000000000 : ℝ)|^4329 ≤ (192209018127/1562500000000 : ℝ)^3305
        have hw : |(-1009694377/5000000000 : ℝ)|=(1009694377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(523463847/1000000000 : ℝ)|^4329 ≤ (42833972009711/100000000000000 : ℝ)^3305
        have hw : |(523463847/1000000000 : ℝ)|=(523463847/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423058951/10000000000 : ℝ)|^4329 ≤ (8972930162267/20000000000000 : ℝ)^3305
        have hw : |(5423058951/10000000000 : ℝ)|=(5423058951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s3_5 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5302638543/10000000000 : ℝ)*x 0 + (-38544063/200000000 : ℝ)*x 1 + (5423058949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302638543/10000000000 : ℝ)^4329 ≤ (1089106647793/2500000000000 : ℝ)^3305 := by
    have hnat : (5302638543 : ℕ)^4329*2500000000000^3305 ≤ 1089106647793^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302638543 10000000000 1089106647793 2500000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38544063/200000000 : ℝ)^4329 ≤ (11571083279717/100000000000000 : ℝ)^3305 := by
    have hnat : (38544063 : ℕ)^4329*100000000000000^3305 ≤ 11571083279717^3305*200000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38544063 200000000 11571083279717 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5423058949/10000000000 : ℝ)^4329 ≤ (22432325394831/50000000000000 : ℝ)^3305 := by
    have hnat : (5423058949 : ℕ)^4329*50000000000000^3305 ≤ 22432325394831^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423058949 10000000000 22432325394831 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302638543/10000000000 : ℝ), (-38544063/200000000 : ℝ), (5423058949/10000000000 : ℝ)] ![(1089106647793/2500000000000 : ℝ), (11571083279717/100000000000000 : ℝ), (22432325394831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302638543/10000000000 : ℝ)|^4329 ≤ (1089106647793/2500000000000 : ℝ)^3305
        have hw : |(5302638543/10000000000 : ℝ)|=(5302638543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-38544063/200000000 : ℝ)|^4329 ≤ (11571083279717/100000000000000 : ℝ)^3305
        have hw : |(-38544063/200000000 : ℝ)|=(38544063/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5423058949/10000000000 : ℝ)|^4329 ≤ (22432325394831/50000000000000 : ℝ)^3305
        have hw : |(5423058949/10000000000 : ℝ)|=(5423058949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s3_6 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5302638459/10000000000 : ℝ)*x 0 + (2711529507/5000000000 : ℝ)*x 1 + (-240900397/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302638459/10000000000 : ℝ)^4329 ≤ (2722766562987/6250000000000 : ℝ)^3305 := by
    have hnat : (5302638459 : ℕ)^4329*6250000000000^3305 ≤ 2722766562987^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302638459 10000000000 2722766562987 6250000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2711529507/5000000000 : ℝ)^4329 ≤ (22432325747007/50000000000000 : ℝ)^3305 := by
    have hnat : (2711529507 : ℕ)^4329*50000000000000^3305 ≤ 22432325747007^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711529507 5000000000 22432325747007 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (240900397/1250000000 : ℝ)^4329 ≤ (1157108348419/10000000000000 : ℝ)^3305 := by
    have hnat : (240900397 : ℕ)^4329*10000000000000^3305 ≤ 1157108348419^3305*1250000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240900397 1250000000 1157108348419 10000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302638459/10000000000 : ℝ), (2711529507/5000000000 : ℝ), (-240900397/1250000000 : ℝ)] ![(2722766562987/6250000000000 : ℝ), (22432325747007/50000000000000 : ℝ), (1157108348419/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302638459/10000000000 : ℝ)|^4329 ≤ (2722766562987/6250000000000 : ℝ)^3305
        have hw : |(5302638459/10000000000 : ℝ)|=(5302638459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2711529507/5000000000 : ℝ)|^4329 ≤ (22432325747007/50000000000000 : ℝ)^3305
        have hw : |(2711529507/5000000000 : ℝ)|=(2711529507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-240900397/1250000000 : ℝ)|^4329 ≤ (1157108348419/10000000000000 : ℝ)^3305
        have hw : |(-240900397/1250000000 : ℝ)|=(240900397/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s3_7 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4318734421/10000000000 : ℝ)*x 0 + (4522354941/10000000000 : ℝ)*x 1 + (824736359/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4318734421/10000000000 : ℝ)^4329 ≤ (16647449219033/50000000000000 : ℝ)^3305 := by
    have hnat : (4318734421 : ℕ)^4329*50000000000000^3305 ≤ 16647449219033^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4318734421 10000000000 16647449219033 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4522354941/10000000000 : ℝ)^4329 ≤ (17682963156379/50000000000000 : ℝ)^3305 := by
    have hnat : (4522354941 : ℕ)^4329*50000000000000^3305 ≤ 17682963156379^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4522354941 10000000000 17682963156379 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (824736359/2000000000 : ℝ)^4329 ≤ (31339175227497/100000000000000 : ℝ)^3305 := by
    have hnat : (824736359 : ℕ)^4329*100000000000000^3305 ≤ 31339175227497^3305*2000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824736359 2000000000 31339175227497 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4318734421/10000000000 : ℝ), (4522354941/10000000000 : ℝ), (824736359/2000000000 : ℝ)] ![(16647449219033/50000000000000 : ℝ), (17682963156379/50000000000000 : ℝ), (31339175227497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4318734421/10000000000 : ℝ)|^4329 ≤ (16647449219033/50000000000000 : ℝ)^3305
        have hw : |(4318734421/10000000000 : ℝ)|=(4318734421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4522354941/10000000000 : ℝ)|^4329 ≤ (17682963156379/50000000000000 : ℝ)^3305
        have hw : |(4522354941/10000000000 : ℝ)|=(4522354941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(824736359/2000000000 : ℝ)|^4329 ≤ (31339175227497/100000000000000 : ℝ)^3305
        have hw : |(824736359/2000000000 : ℝ)|=(824736359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1369_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77896747/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16001/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10023/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2193/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7493/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16001/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10023/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16001/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10023/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16001/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10023/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16001/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10023/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16001/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10023/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16001/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10023/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10023/100000 : ℝ) ^ (541/128 : ℝ) ≤ (2996570322659401/50000000000000000000 : ℝ) := by
    have hpowers : (10023/100000 : ℝ)^541 ≤ (2996570322659401/50000000000000000000 : ℝ)^128 := by
      have hnat : (10023 : ℕ)^541*50000000000000000000^128 ≤ 2996570322659401^128*100000^541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10023 100000 2996570322659401 50000000000000000000 541 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10023/100000 : ℝ)) (X := (2996570322659401/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hpowhi : (16001/100000 : ℝ) ^ (541/128 : ℝ) ≤ (43279086345467267/100000000000000000000 : ℝ) := by
    have hpowers : (16001/100000 : ℝ)^541 ≤ (43279086345467267/100000000000000000000 : ℝ)^128 := by
      have hnat : (16001 : ℕ)^541*100000000000000000000^128 ≤ 43279086345467267^128*100000^541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16001 100000 43279086345467267 100000000000000000000 541 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16001/100000 : ℝ)) (X := (43279086345467267/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002996570322659401/25000000000000000000 : ℝ) ≤ (1250035447638999/1250000000000000 : ℝ) ^ (541/128 : ℝ) := by
    have hpowers : (25002996570322659401/25000000000000000000 : ℝ)^128 ≤ (1250035447638999/1250000000000000 : ℝ)^541 := by
      have hnat : (25002996570322659401 : ℕ)^128*1250000000000000^541 ≤ 1250035447638999^541*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002996570322659401 25000000000000000000 1250035447638999 1250000000000000 128 541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250035447638999/1250000000000000 : ℝ)) (X := (25002996570322659401/25000000000000000000 : ℝ)) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (100049272226990786069/100000000000000000000 : ℝ) ≤ (1250145694529921/1250000000000000 : ℝ) ^ (541/128 : ℝ) := by
    have hpowers : (100049272226990786069/100000000000000000000 : ℝ)^128 ≤ (1250145694529921/1250000000000000 : ℝ)^541 := by
      have hnat : (100049272226990786069 : ℕ)^128*1250000000000000^541 ≤ 1250145694529921^541*100000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100049272226990786069 100000000000000000000 1250145694529921 1250000000000000 128 541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250145694529921/1250000000000000 : ℝ)) (X := (100049272226990786069/100000000000000000000 : ℝ)) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50043279086345467267/50000000000000000000 : ℝ) ≤ (1250255941420843/1250000000000000 : ℝ) ^ (541/128 : ℝ) := by
    have hpowers : (50043279086345467267/50000000000000000000 : ℝ)^128 ≤ (1250255941420843/1250000000000000 : ℝ)^541 := by
      have hnat : (50043279086345467267 : ℕ)^128*1250000000000000^541 ≤ 1250255941420843^541*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50043279086345467267 50000000000000000000 1250255941420843 1250000000000000 128 541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250255941420843/1250000000000000 : ℝ)) (X := (50043279086345467267/50000000000000000000 : ℝ)) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2996570322659401/50000000000000000000 : ℝ) ≤ ((106721455668721623/106750000000000000 : ℝ)+2*(7874777923/5337500000000 : ℝ)*(10023/100000 : ℝ))^(541/128 : ℝ) := by
    rw [show (106721455668721623/106750000000000000 : ℝ)+2*(7874777923/5337500000000 : ℝ)*(10023/100000 : ℝ)=(1250035447638999/1250000000000000 : ℝ) by norm_num, show 1+2*(2996570322659401/50000000000000000000 : ℝ)=(25002996570322659401/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(43279086345467267/100000000000000000000 : ℝ)+(2996570322659401/50000000000000000000 : ℝ) ≤ ((106721455668721623/106750000000000000 : ℝ)+(7874777923/5337500000000 : ℝ)*((16001/100000 : ℝ)+(10023/100000 : ℝ)))^(541/128 : ℝ) := by
    rw [show (106721455668721623/106750000000000000 : ℝ)+(7874777923/5337500000000 : ℝ)*((16001/100000 : ℝ)+(10023/100000 : ℝ))=(1250145694529921/1250000000000000 : ℝ) by norm_num, show 1+(43279086345467267/100000000000000000000 : ℝ)+(2996570322659401/50000000000000000000 : ℝ)=(100049272226990786069/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(43279086345467267/100000000000000000000 : ℝ) ≤ ((106721455668721623/106750000000000000 : ℝ)+2*(7874777923/5337500000000 : ℝ)*(16001/100000 : ℝ))^(541/128 : ℝ) := by
    rw [show (106721455668721623/106750000000000000 : ℝ)+2*(7874777923/5337500000000 : ℝ)*(16001/100000 : ℝ)=(1250255941420843/1250000000000000 : ℝ) by norm_num, show 1+2*(43279086345467267/100000000000000000000 : ℝ)=(50043279086345467267/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (106721455668721623/106750000000000000 : ℝ)*(X 1 0+X 2 0)+(7874777923/5337500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (541/128 : ℝ)) (lo := (10023/100000 : ℝ)) (hi := (16001/100000 : ℝ)) (c := (106721455668721623/106750000000000000 : ℝ)) (alpha := (7874777923/5337500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (106721455668721623/106750000000000000 : ℝ)*(X 0 1+X 2 1)+(7874777923/5337500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (541/128 : ℝ)) (lo := (10023/100000 : ℝ)) (hi := (16001/100000 : ℝ)) (c := (106721455668721623/106750000000000000 : ℝ)) (alpha := (7874777923/5337500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (106721455668721623/106750000000000000 : ℝ)*(X 0 2+X 1 2)+(7874777923/5337500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (541/128 : ℝ)) (lo := (10023/100000 : ℝ)) (hi := (16001/100000 : ℝ)) (c := (106721455668721623/106750000000000000 : ℝ)) (alpha := (7874777923/5337500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2019370851/10000000000 : ℝ)*X 0 0+(5423843459/10000000000 : ℝ)*X 0 1+(1308464653/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267586171/500000000 : ℝ)*X 1 0+(-1058201723/5000000000 : ℝ)*X 1 1+(5233858737/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351723441/10000000000 : ℝ)*X 2 0+(654232317/1250000000 : ℝ)*X 2 1+(-529100921/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4318696807/10000000000 : ℝ)*X 0 0+(4122021841/10000000000 : ℝ)*X 0 1+(4524004991/10000000000 : ℝ)*X 0 2+(4318696807/10000000000 : ℝ)*X 1 0+(4122021841/10000000000 : ℝ)*X 1 1+(4524004991/10000000000 : ℝ)*X 1 2+(4318696807/10000000000 : ℝ)*X 2 0+(4122021841/10000000000 : ℝ)*X 2 1+(4524004991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1009694377/5000000000 : ℝ)*X 0 0+(523463847/1000000000 : ℝ)*X 0 1+(5423058951/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302638543/10000000000 : ℝ)*X 1 0+(-38544063/200000000 : ℝ)*X 1 1+(5423058949/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5302638459/10000000000 : ℝ)*X 2 0+(2711529507/5000000000 : ℝ)*X 2 1+(-240900397/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4318734421/10000000000 : ℝ)*X 0 0+(4522354941/10000000000 : ℝ)*X 0 1+(824736359/2000000000 : ℝ)*X 0 2+(4318734421/10000000000 : ℝ)*X 1 0+(4522354941/10000000000 : ℝ)*X 1 1+(824736359/2000000000 : ℝ)*X 1 2+(4318734421/10000000000 : ℝ)*X 2 0+(4522354941/10000000000 : ℝ)*X 2 1+(824736359/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5920762766052171641862891/2668750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (112019751/50000000000000 : ℝ)*(base19) + (80164969/20000000000000 : ℝ)*(base23) + (102541389/100000000000000 : ℝ)*(upper3) + (21928831/25000000000000 : ℝ)*(lower4) + (3875631110861711/100000000000000 : ℝ)*(major0) + (3875631110861711/100000000000000 : ℝ)*(major1) + (3875631110861711/100000000000000 : ℝ)*(major2) + (1052717291447593/20000000000000 : ℝ)*(sp0) + (5263589934771107/100000000000000 : ℝ)*(sp1) + (82243576731803/1562500000000 : ℝ)*(sp2) + (1243834414901833/50000000000000 : ℝ)*(sp3) + (3701572643/100000000000000 : ℝ)*(sp4) + (847150371/100000000000000 : ℝ)*(sp6) + (1579578691/50000000000000 : ℝ)*(sp7) + (310958998620131/12500000000000 : ℝ)*(f.failure) + (5263590158810609/100000000000000 : ℝ)*(f.sum) + (238485047679/2135000000000000000000000000 : ℝ)*base65 + (9921543346819721/1525000000000000000000000000000 : ℝ)*base68 + (11183466842780279/1525000000000000000000000000000 : ℝ)*base69 + (900503998905279/1525000000000000000000000000000 : ℝ)*base71 + (1302850656907/1067500000000000000000000000 : ℝ)*base73 + (9322006419130279/1525000000000000000000000000000 : ℝ)*base75 + (3327821761880279/1525000000000000000000000000000 : ℝ)*base77 + (7225551832655279/1525000000000000000000000000000 : ℝ)*base79 + (331249596519/133437500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (136143/625000000000000000000 : ℝ)*base90 + (136143/625000000000000000000 : ℝ)*base92 + (136143/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1800881393681262794993157/190625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1700440761/100000000000000 : ℝ)*(base19) + (1757583239/100000000000000 : ℝ)*(base23) + (37399011/20000000000000 : ℝ)*(upper3) + (14029291/20000000000000 : ℝ)*(lower4) + (102027633/50000000000000 : ℝ)*(upper5) + (976949640378943/25000000000000 : ℝ)*(major0) + (976949640378943/25000000000000 : ℝ)*(major1) + (976949640378943/25000000000000 : ℝ)*(major2) + (1559790017/5000000000000 : ℝ)*(sp1) + (16080219037/50000000000000 : ℝ)*(sp2) + (5307277326235469/100000000000000 : ℝ)*(sp4) + (41462847109331/781250000000 : ℝ)*(sp5) + (5307243408214157/100000000000000 : ℝ)*(sp6) + (1254159740943923/50000000000000 : ℝ)*(sp7) + (1254159740943923/50000000000000 : ℝ)*(f.failure) + (5307277326235469/100000000000000 : ℝ)*(f.sum) + (220126575909/76250000000000000000000000 : ℝ)*base66 + (2831311288919927/381250000000000000000000000000 : ℝ)*base67 + (2210004529838677/381250000000000000000000000000 : ℝ)*base69 + (1433230834457427/381250000000000000000000000000 : ℝ)*base71 + (172293069483/152500000000000000000000000 : ℝ)*base74 + (9330063002507427/381250000000000000000000000000 : ℝ)*base75 + (434558631626177/381250000000000000000000000000 : ℝ)*base77 + (1092937699219927/381250000000000000000000000000 : ℝ)*base79 + (1161380631073/152500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (11118481/2500000000000000000000 : ℝ)*base89 + (11118481/2500000000000000000000 : ℝ)*base91 + (11118481/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1369_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77896747/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16001/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10023/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2193/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7493/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1369_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1369_s4_0 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-252578407/1250000000 : ℝ)*x 0 + (1082685363/2000000000 : ℝ)*x 1 + (5243449659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (252578407/1250000000 : ℝ)^4329 ≤ (12311260139529/100000000000000 : ℝ)^3305 := by
    have hnat : (252578407 : ℕ)^4329*100000000000000^3305 ≤ 12311260139529^3305*1250000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252578407 1250000000 12311260139529 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082685363/2000000000 : ℝ)^4329 ≤ (4476030401233/10000000000000 : ℝ)^3305 := by
    have hnat : (1082685363 : ℕ)^4329*10000000000000^3305 ≤ 4476030401233^3305*2000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082685363 2000000000 4476030401233 10000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243449659/10000000000 : ℝ)^4329 ≤ (10732108956367/25000000000000 : ℝ)^3305 := by
    have hnat : (5243449659 : ℕ)^4329*25000000000000^3305 ≤ 10732108956367^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243449659 10000000000 10732108956367 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-252578407/1250000000 : ℝ), (1082685363/2000000000 : ℝ), (5243449659/10000000000 : ℝ)] ![(12311260139529/100000000000000 : ℝ), (4476030401233/10000000000000 : ℝ), (10732108956367/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-252578407/1250000000 : ℝ)|^4329 ≤ (12311260139529/100000000000000 : ℝ)^3305
        have hw : |(-252578407/1250000000 : ℝ)|=(252578407/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082685363/2000000000 : ℝ)|^4329 ≤ (4476030401233/10000000000000 : ℝ)^3305
        have hw : |(1082685363/2000000000 : ℝ)|=(1082685363/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243449659/10000000000 : ℝ)|^4329 ≤ (10732108956367/25000000000000 : ℝ)^3305
        have hw : |(5243449659/10000000000 : ℝ)|=(5243449659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s4_1 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674529097/5000000000 : ℝ)*x 0 + (-1053624387/5000000000 : ℝ)*x 1 + (1310862529/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674529097/5000000000 : ℝ)^4329 ≤ (44064465994303/100000000000000 : ℝ)^3305 := by
    have hnat : (2674529097 : ℕ)^4329*100000000000000^3305 ≤ 44064465994303^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674529097 5000000000 44064465994303 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053624387/5000000000 : ℝ)^4329 ≤ (6503546634159/50000000000000 : ℝ)^3305 := by
    have hnat : (1053624387 : ℕ)^4329*50000000000000^3305 ≤ 6503546634159^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053624387 5000000000 6503546634159 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310862529/2500000000 : ℝ)^4329 ≤ (42928440726193/100000000000000 : ℝ)^3305 := by
    have hnat : (1310862529 : ℕ)^4329*100000000000000^3305 ≤ 42928440726193^3305*2500000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310862529 2500000000 42928440726193 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674529097/5000000000 : ℝ), (-1053624387/5000000000 : ℝ), (1310862529/2500000000 : ℝ)] ![(44064465994303/100000000000000 : ℝ), (6503546634159/50000000000000 : ℝ), (42928440726193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674529097/5000000000 : ℝ)|^4329 ≤ (44064465994303/100000000000000 : ℝ)^3305
        have hw : |(2674529097/5000000000 : ℝ)|=(2674529097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1053624387/5000000000 : ℝ)|^4329 ≤ (6503546634159/50000000000000 : ℝ)^3305
        have hw : |(-1053624387/5000000000 : ℝ)|=(1053624387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310862529/2500000000 : ℝ)|^4329 ≤ (42928440726193/100000000000000 : ℝ)^3305
        have hw : |(1310862529/2500000000 : ℝ)|=(1310862529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s4_2 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674529099/5000000000 : ℝ)*x 0 + (2621724781/5000000000 : ℝ)*x 1 + (-2107249503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674529099/5000000000 : ℝ)^4329 ≤ (5508058254683/12500000000000 : ℝ)^3305 := by
    have hnat : (2674529099 : ℕ)^4329*12500000000000^3305 ≤ 5508058254683^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674529099 5000000000 5508058254683 12500000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2621724781/5000000000 : ℝ)^4329 ≤ (42928434785271/100000000000000 : ℝ)^3305 := by
    have hnat : (2621724781 : ℕ)^4329*100000000000000^3305 ≤ 42928434785271^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621724781 5000000000 42928434785271 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2107249503/10000000000 : ℝ)^4329 ≤ (13007099162291/100000000000000 : ℝ)^3305 := by
    have hnat : (2107249503 : ℕ)^4329*100000000000000^3305 ≤ 13007099162291^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107249503 10000000000 13007099162291 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674529099/5000000000 : ℝ), (2621724781/5000000000 : ℝ), (-2107249503/10000000000 : ℝ)] ![(5508058254683/12500000000000 : ℝ), (42928434785271/100000000000000 : ℝ), (13007099162291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674529099/5000000000 : ℝ)|^4329 ≤ (5508058254683/12500000000000 : ℝ)^3305
        have hw : |(2674529099/5000000000 : ℝ)|=(2674529099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2621724781/5000000000 : ℝ)|^4329 ≤ (42928434785271/100000000000000 : ℝ)^3305
        have hw : |(2621724781/5000000000 : ℝ)|=(2621724781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2107249503/10000000000 : ℝ)|^4329 ≤ (13007099162291/100000000000000 : ℝ)^3305
        have hw : |(-2107249503/10000000000 : ℝ)|=(2107249503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s4_3 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4319463699/10000000000 : ℝ)*x 0 + (4143093781/10000000000 : ℝ)*x 1 + (225137213/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319463699/10000000000 : ℝ)^4329 ≤ (33302262913051/100000000000000 : ℝ)^3305 := by
    have hnat : (4319463699 : ℕ)^4329*100000000000000^3305 ≤ 33302262913051^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319463699 10000000000 33302262913051 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4143093781/10000000000 : ℝ)^4329 ≤ (246348064093/781250000000 : ℝ)^3305 := by
    have hnat : (4143093781 : ℕ)^4329*781250000000^3305 ≤ 246348064093^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4143093781 10000000000 246348064093 781250000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225137213/500000000 : ℝ)^4329 ≤ (35165184866009/100000000000000 : ℝ)^3305 := by
    have hnat : (225137213 : ℕ)^4329*100000000000000^3305 ≤ 35165184866009^3305*500000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225137213 500000000 35165184866009 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319463699/10000000000 : ℝ), (4143093781/10000000000 : ℝ), (225137213/500000000 : ℝ)] ![(33302262913051/100000000000000 : ℝ), (246348064093/781250000000 : ℝ), (35165184866009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319463699/10000000000 : ℝ)|^4329 ≤ (33302262913051/100000000000000 : ℝ)^3305
        have hw : |(4319463699/10000000000 : ℝ)|=(4319463699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4143093781/10000000000 : ℝ)|^4329 ≤ (246348064093/781250000000 : ℝ)^3305
        have hw : |(4143093781/10000000000 : ℝ)|=(4143093781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(225137213/500000000 : ℝ)|^4329 ≤ (35165184866009/100000000000000 : ℝ)^3305
        have hw : |(225137213/500000000 : ℝ)|=(225137213/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s4_4 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2020639881/10000000000 : ℝ)*x 0 + (5244074401/10000000000 : ℝ)*x 1 + (5412798893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2020639881/10000000000 : ℝ)^4329 ≤ (12311360893977/100000000000000 : ℝ)^3305 := by
    have hnat : (2020639881 : ℕ)^4329*100000000000000^3305 ≤ 12311360893977^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020639881 10000000000 12311360893977 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244074401/10000000000 : ℝ)^4329 ≤ (21467567743041/50000000000000 : ℝ)^3305 := by
    have hnat : (5244074401 : ℕ)^4329*50000000000000^3305 ≤ 21467567743041^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244074401 10000000000 21467567743041 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412798893/10000000000 : ℝ)^4329 ≤ (2237675180369/5000000000000 : ℝ)^3305 := by
    have hnat : (5412798893 : ℕ)^4329*5000000000000^3305 ≤ 2237675180369^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412798893 10000000000 2237675180369 5000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2020639881/10000000000 : ℝ), (5244074401/10000000000 : ℝ), (5412798893/10000000000 : ℝ)] ![(12311360893977/100000000000000 : ℝ), (21467567743041/50000000000000 : ℝ), (2237675180369/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2020639881/10000000000 : ℝ)|^4329 ≤ (12311360893977/100000000000000 : ℝ)^3305
        have hw : |(-2020639881/10000000000 : ℝ)|=(2020639881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244074401/10000000000 : ℝ)|^4329 ≤ (21467567743041/50000000000000 : ℝ)^3305
        have hw : |(5244074401/10000000000 : ℝ)|=(5244074401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412798893/10000000000 : ℝ)|^4329 ≤ (2237675180369/5000000000000 : ℝ)^3305
        have hw : |(5412798893/10000000000 : ℝ)|=(5412798893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s4_5 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663142873/1250000000 : ℝ)*x 0 + (-387579987/2000000000 : ℝ)*x 1 + (5412798833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663142873/1250000000 : ℝ)^4329 ≤ (43591218288831/100000000000000 : ℝ)^3305 := by
    have hnat : (663142873 : ℕ)^4329*100000000000000^3305 ≤ 43591218288831^3305*1250000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663142873 1250000000 43591218288831 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (387579987/2000000000 : ℝ)^4329 ≤ (11655278745709/100000000000000 : ℝ)^3305 := by
    have hnat : (387579987 : ℕ)^4329*100000000000000^3305 ≤ 11655278745709^3305*2000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387579987 2000000000 11655278745709 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412798833/10000000000 : ℝ)^4329 ≤ (44753502957591/100000000000000 : ℝ)^3305 := by
    have hnat : (5412798833 : ℕ)^4329*100000000000000^3305 ≤ 44753502957591^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412798833 10000000000 44753502957591 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663142873/1250000000 : ℝ), (-387579987/2000000000 : ℝ), (5412798833/10000000000 : ℝ)] ![(43591218288831/100000000000000 : ℝ), (11655278745709/100000000000000 : ℝ), (44753502957591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663142873/1250000000 : ℝ)|^4329 ≤ (43591218288831/100000000000000 : ℝ)^3305
        have hw : |(663142873/1250000000 : ℝ)|=(663142873/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-387579987/2000000000 : ℝ)|^4329 ≤ (11655278745709/100000000000000 : ℝ)^3305
        have hw : |(-387579987/2000000000 : ℝ)|=(387579987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412798833/10000000000 : ℝ)|^4329 ≤ (44753502957591/100000000000000 : ℝ)^3305
        have hw : |(5412798833/10000000000 : ℝ)|=(5412798833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s4_6 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305142939/10000000000 : ℝ)*x 0 + (2706399467/5000000000 : ℝ)*x 1 + (-1937899857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305142939/10000000000 : ℝ)^4329 ≤ (43591217804513/100000000000000 : ℝ)^3305 := by
    have hnat : (5305142939 : ℕ)^4329*100000000000000^3305 ≤ 43591217804513^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305142939 10000000000 43591217804513 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706399467/5000000000 : ℝ)^4329 ≤ (22376752025701/50000000000000 : ℝ)^3305 := by
    have hnat : (2706399467 : ℕ)^4329*50000000000000^3305 ≤ 22376752025701^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706399467 5000000000 22376752025701 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1937899857/10000000000 : ℝ)^4329 ≤ (11655278131237/100000000000000 : ℝ)^3305 := by
    have hnat : (1937899857 : ℕ)^4329*100000000000000^3305 ≤ 11655278131237^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1937899857 10000000000 11655278131237 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305142939/10000000000 : ℝ), (2706399467/5000000000 : ℝ), (-1937899857/10000000000 : ℝ)] ![(43591217804513/100000000000000 : ℝ), (22376752025701/50000000000000 : ℝ), (11655278131237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305142939/10000000000 : ℝ)|^4329 ≤ (43591217804513/100000000000000 : ℝ)^3305
        have hw : |(5305142939/10000000000 : ℝ)|=(5305142939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706399467/5000000000 : ℝ)|^4329 ≤ (22376752025701/50000000000000 : ℝ)^3305
        have hw : |(2706399467/5000000000 : ℝ)|=(2706399467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1937899857/10000000000 : ℝ)|^4329 ≤ (11655278131237/100000000000000 : ℝ)^3305
        have hw : |(-1937899857/10000000000 : ℝ)|=(1937899857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s4_7 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4319489989/10000000000 : ℝ)*x 0 + (4501422571/10000000000 : ℝ)*x 1 + (4144423243/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319489989/10000000000 : ℝ)^4329 ≤ (8325632101201/25000000000000 : ℝ)^3305 := by
    have hnat : (4319489989 : ℕ)^4329*25000000000000^3305 ≤ 8325632101201^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319489989 10000000000 8325632101201 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4501422571/10000000000 : ℝ)^4329 ≤ (7030333069213/20000000000000 : ℝ)^3305 := by
    have hnat : (4501422571 : ℕ)^4329*20000000000000^3305 ≤ 7030333069213^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501422571 10000000000 7030333069213 20000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4144423243/10000000000 : ℝ)^4329 ≤ (7886451558839/25000000000000 : ℝ)^3305 := by
    have hnat : (4144423243 : ℕ)^4329*25000000000000^3305 ≤ 7886451558839^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4144423243 10000000000 7886451558839 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319489989/10000000000 : ℝ), (4501422571/10000000000 : ℝ), (4144423243/10000000000 : ℝ)] ![(8325632101201/25000000000000 : ℝ), (7030333069213/20000000000000 : ℝ), (7886451558839/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319489989/10000000000 : ℝ)|^4329 ≤ (8325632101201/25000000000000 : ℝ)^3305
        have hw : |(4319489989/10000000000 : ℝ)|=(4319489989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4501422571/10000000000 : ℝ)|^4329 ≤ (7030333069213/20000000000000 : ℝ)^3305
        have hw : |(4501422571/10000000000 : ℝ)|=(4501422571/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4144423243/10000000000 : ℝ)|^4329 ≤ (7886451558839/25000000000000 : ℝ)^3305
        have hw : |(4144423243/10000000000 : ℝ)|=(4144423243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1369_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77896747/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7493/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2193/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11169/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (923/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7493/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2193/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7493/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2193/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7493/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2193/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7493/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2193/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7493/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2193/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7493/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2193/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2193/20000 : ℝ) ^ (541/128 : ℝ) ≤ (876065344199821/10000000000000000000 : ℝ) := by
    have hpowers : (2193/20000 : ℝ)^541 ≤ (876065344199821/10000000000000000000 : ℝ)^128 := by
      have hnat : (2193 : ℕ)^541*10000000000000000000^128 ≤ 876065344199821^128*20000^541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2193 20000 876065344199821 10000000000000000000 541 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2193/20000 : ℝ)) (X := (876065344199821/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hpowhi : (7493/50000 : ℝ) ^ (541/128 : ℝ) ≤ (16404168257437951/50000000000000000000 : ℝ) := by
    have hpowers : (7493/50000 : ℝ)^541 ≤ (16404168257437951/50000000000000000000 : ℝ)^128 := by
      have hnat : (7493 : ℕ)^541*50000000000000000000^128 ≤ 16404168257437951^128*50000^541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7493 50000 16404168257437951 50000000000000000000 541 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7493/50000 : ℝ)) (X := (16404168257437951/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000876065344199821/5000000000000000000 : ℝ) ≤ (10000414524455713/10000000000000000 : ℝ) ^ (541/128 : ℝ) := by
    have hpowers : (5000876065344199821/5000000000000000000 : ℝ)^128 ≤ (10000414524455713/10000000000000000 : ℝ)^541 := by
      have hnat : (5000876065344199821 : ℕ)^128*10000000000000000^541 ≤ 10000414524455713^541*5000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000876065344199821 5000000000000000000 10000414524455713 10000000000000000 128 541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000414524455713/10000000000000000 : ℝ)) (X := (5000876065344199821/5000000000000000000 : ℝ)) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (781574757734038079/781250000000000000 : ℝ) ≤ (2500245840419107/2500000000000000 : ℝ) ^ (541/128 : ℝ) := by
    have hpowers : (781574757734038079/781250000000000000 : ℝ)^128 ≤ (2500245840419107/2500000000000000 : ℝ)^541 := by
      have hnat : (781574757734038079 : ℕ)^128*2500000000000000^541 ≤ 2500245840419107^541*781250000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781574757734038079 781250000000000000 2500245840419107 2500000000000000 128 541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500245840419107/2500000000000000 : ℝ)) (X := (781574757734038079/781250000000000000 : ℝ)) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016404168257437951/25000000000000000000 : ℝ) ≤ (10001552198897143/10000000000000000 : ℝ) ^ (541/128 : ℝ) := by
    have hpowers : (25016404168257437951/25000000000000000000 : ℝ)^128 ≤ (10001552198897143/10000000000000000 : ℝ)^541 := by
      have hnat : (25016404168257437951 : ℕ)^128*10000000000000000^541 ≤ 10001552198897143^541*25000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016404168257437951 25000000000000000000 10001552198897143 10000000000000000 128 541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001552198897143/10000000000000000 : ℝ)) (X := (25016404168257437951/25000000000000000000 : ℝ)) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(876065344199821/10000000000000000000 : ℝ) ≤ ((40199192202586142023/40210000000000000000 : ℝ)+2*(113767444143/80420000000000 : ℝ)*(2193/20000 : ℝ))^(541/128 : ℝ) := by
    rw [show (40199192202586142023/40210000000000000000 : ℝ)+2*(113767444143/80420000000000 : ℝ)*(2193/20000 : ℝ)=(10000414524455713/10000000000000000 : ℝ) by norm_num, show 1+2*(876065344199821/10000000000000000000 : ℝ)=(5000876065344199821/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16404168257437951/50000000000000000000 : ℝ)+(876065344199821/10000000000000000000 : ℝ) ≤ ((40199192202586142023/40210000000000000000 : ℝ)+(113767444143/80420000000000 : ℝ)*((7493/50000 : ℝ)+(2193/20000 : ℝ)))^(541/128 : ℝ) := by
    rw [show (40199192202586142023/40210000000000000000 : ℝ)+(113767444143/80420000000000 : ℝ)*((7493/50000 : ℝ)+(2193/20000 : ℝ))=(2500245840419107/2500000000000000 : ℝ) by norm_num, show 1+(16404168257437951/50000000000000000000 : ℝ)+(876065344199821/10000000000000000000 : ℝ)=(781574757734038079/781250000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16404168257437951/50000000000000000000 : ℝ) ≤ ((40199192202586142023/40210000000000000000 : ℝ)+2*(113767444143/80420000000000 : ℝ)*(7493/50000 : ℝ))^(541/128 : ℝ) := by
    rw [show (40199192202586142023/40210000000000000000 : ℝ)+2*(113767444143/80420000000000 : ℝ)*(7493/50000 : ℝ)=(10001552198897143/10000000000000000 : ℝ) by norm_num, show 1+2*(16404168257437951/50000000000000000000 : ℝ)=(25016404168257437951/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (40199192202586142023/40210000000000000000 : ℝ)*(X 1 0+X 2 0)+(113767444143/80420000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (541/128 : ℝ)) (lo := (2193/20000 : ℝ)) (hi := (7493/50000 : ℝ)) (c := (40199192202586142023/40210000000000000000 : ℝ)) (alpha := (113767444143/80420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (40199192202586142023/40210000000000000000 : ℝ)*(X 0 1+X 2 1)+(113767444143/80420000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (541/128 : ℝ)) (lo := (2193/20000 : ℝ)) (hi := (7493/50000 : ℝ)) (c := (40199192202586142023/40210000000000000000 : ℝ)) (alpha := (113767444143/80420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (40199192202586142023/40210000000000000000 : ℝ)*(X 0 2+X 1 2)+(113767444143/80420000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (541/128 : ℝ)) (lo := (2193/20000 : ℝ)) (hi := (7493/50000 : ℝ)) (c := (40199192202586142023/40210000000000000000 : ℝ)) (alpha := (113767444143/80420000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-252578407/1250000000 : ℝ)*X 0 0+(1082685363/2000000000 : ℝ)*X 0 1+(5243449659/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674529097/5000000000 : ℝ)*X 1 0+(-1053624387/5000000000 : ℝ)*X 1 1+(1310862529/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674529099/5000000000 : ℝ)*X 2 0+(2621724781/5000000000 : ℝ)*X 2 1+(-2107249503/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4319463699/10000000000 : ℝ)*X 0 0+(4143093781/10000000000 : ℝ)*X 0 1+(225137213/500000000 : ℝ)*X 0 2+(4319463699/10000000000 : ℝ)*X 1 0+(4143093781/10000000000 : ℝ)*X 1 1+(225137213/500000000 : ℝ)*X 1 2+(4319463699/10000000000 : ℝ)*X 2 0+(4143093781/10000000000 : ℝ)*X 2 1+(225137213/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2020639881/10000000000 : ℝ)*X 0 0+(5244074401/10000000000 : ℝ)*X 0 1+(5412798893/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663142873/1250000000 : ℝ)*X 1 0+(-387579987/2000000000 : ℝ)*X 1 1+(5412798833/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305142939/10000000000 : ℝ)*X 2 0+(2706399467/5000000000 : ℝ)*X 2 1+(-1937899857/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4319489989/10000000000 : ℝ)*X 0 0+(4501422571/10000000000 : ℝ)*X 0 1+(4144423243/10000000000 : ℝ)*X 0 2+(4319489989/10000000000 : ℝ)*X 1 0+(4501422571/10000000000 : ℝ)*X 1 1+(4144423243/10000000000 : ℝ)*X 1 2+(4319489989/10000000000 : ℝ)*X 2 0+(4501422571/10000000000 : ℝ)*X 2 1+(4144423243/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8714379156288629575241012067/1005250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (480428723/25000000000000 : ℝ)*(base19) + (4150033/195312500000 : ℝ)*(base23) + (169677153/25000000000000 : ℝ)*(upper3) + (112872809/100000000000000 : ℝ)*(lower4) + (2165939242286019/50000000000000 : ℝ)*(major0) + (2165939242286019/50000000000000 : ℝ)*(major1) + (2165939242286019/50000000000000 : ℝ)*(major2) + (1470800246071241/25000000000000 : ℝ)*(sp0) + (2941614418518283/50000000000000 : ℝ)*(sp1) + (5883227134306001/100000000000000 : ℝ)*(sp2) + (347562136662369/12500000000000 : ℝ)*(sp3) + (5954893299/20000000000000 : ℝ)*(sp4) + (749814281/50000000000000 : ℝ)*(sp6) + (14414065699/50000000000000 : ℝ)*(sp7) + (55610518428607/2000000000000 : ℝ)*(f.failure) + (2941615379375729/50000000000000 : ℝ)*(f.sum) + (28163851213423/4021000000000000000000000000 : ℝ)*base65 + (7803776008467276437/2010500000000000000000000000000000 : ℝ)*base67 + (17308192356957276437/2010500000000000000000000000000000 : ℝ)*base69 + (12944958354002776437/2010500000000000000000000000000000 : ℝ)*base71 + (318172991007/1005250000000000000000000000 : ℝ)*base73 + (48586095061334776437/2010500000000000000000000000000000 : ℝ)*base75 + (24069561274826776437/2010500000000000000000000000000000 : ℝ)*base77 + (27252608490159776437/2010500000000000000000000000000000 : ℝ)*base79 + (9387534747397/4021000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (958571/100000000000000000000 : ℝ)*base90 + (958571/100000000000000000000 : ℝ)*base92 + (958571/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5869376823946825258295695179/1005250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1255809541/100000000000000 : ℝ)*(base19) + (259128199/20000000000000 : ℝ)*(base23) + (24271641/100000000000000 : ℝ)*(upper2) + (149989723/100000000000000 : ℝ)*(upper3) + (87603067/100000000000000 : ℝ)*(upper5) + (2181986374414191/50000000000000 : ℝ)*(major0) + (2181986374414191/50000000000000 : ℝ)*(major1) + (2181986374414191/50000000000000 : ℝ)*(major2) + (23059782811/100000000000000 : ℝ)*(sp1) + (3552230971/12500000000000 : ℝ)*(sp2) + (5926818865218499/100000000000000 : ℝ)*(sp4) + (1481698637406537/25000000000000 : ℝ)*(sp5) + (740848643966217/12500000000000 : ℝ)*(sp6) + (1400563218907069/50000000000000 : ℝ)*(sp7) + (1400563218907069/50000000000000 : ℝ)*(f.failure) + (5926818865218499/100000000000000 : ℝ)*(f.sum) + (19076126808497/4021000000000000000000000000 : ℝ)*base66 + (1011885718590648393/2010500000000000000000000000000000 : ℝ)*base67 + (20182962590971351607/2010500000000000000000000000000000 : ℝ)*base70 + (34323577719194851607/2010500000000000000000000000000000 : ℝ)*base72 + (15087990485921/2010500000000000000000000000 : ℝ)*base73 + (24531914854377851607/2010500000000000000000000000000000 : ℝ)*base76 + (25453427038815851607/2010500000000000000000000000000000 : ℝ)*base78 + (18097848669710148393/2010500000000000000000000000000000 : ℝ)*base79 + (2980889599353/1005250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (20404543/2500000000000000000000 : ℝ)*base89 + (20404543/2500000000000000000000 : ℝ)*base91 + (20404543/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1369_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77896747/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7493/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2193/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11169/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (923/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1369_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1369_s5_0 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1010418599/5000000000 : ℝ)*x 0 + (2705810297/5000000000 : ℝ)*x 1 + (1049023481/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1010418599/5000000000 : ℝ)^4329 ≤ (6156467808791/50000000000000 : ℝ)^3305 := by
    have hnat : (1010418599 : ℕ)^4329*50000000000000^3305 ≤ 6156467808791^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010418599 5000000000 6156467808791 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705810297/5000000000 : ℝ)^4329 ≤ (11185185817677/25000000000000 : ℝ)^3305 := by
    have hnat : (2705810297 : ℕ)^4329*25000000000000^3305 ≤ 11185185817677^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705810297 5000000000 11185185817677 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049023481/2000000000 : ℝ)^4329 ≤ (1073658027271/2500000000000 : ℝ)^3305 := by
    have hnat : (1049023481 : ℕ)^4329*2500000000000^3305 ≤ 1073658027271^3305*2000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049023481 2000000000 1073658027271 2500000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1010418599/5000000000 : ℝ), (2705810297/5000000000 : ℝ), (1049023481/2000000000 : ℝ)] ![(6156467808791/50000000000000 : ℝ), (11185185817677/25000000000000 : ℝ), (1073658027271/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1010418599/5000000000 : ℝ)|^4329 ≤ (6156467808791/50000000000000 : ℝ)^3305
        have hw : |(-1010418599/5000000000 : ℝ)|=(1010418599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705810297/5000000000 : ℝ)|^4329 ≤ (11185185817677/25000000000000 : ℝ)^3305
        have hw : |(2705810297/5000000000 : ℝ)|=(2705810297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049023481/2000000000 : ℝ)|^4329 ≤ (1073658027271/2500000000000 : ℝ)^3305
        have hw : |(1049023481/2000000000 : ℝ)|=(1049023481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s5_1 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267429709/500000000 : ℝ)*x 0 + (-2105656347/10000000000 : ℝ)*x 1 + (5245117371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267429709/500000000 : ℝ)^4329 ≤ (44059459282903/100000000000000 : ℝ)^3305 := by
    have hnat : (267429709 : ℕ)^4329*100000000000000^3305 ≤ 44059459282903^3305*500000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267429709 500000000 44059459282903 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2105656347/10000000000 : ℝ)^4329 ≤ (1624277498431/12500000000000 : ℝ)^3305 := by
    have hnat : (2105656347 : ℕ)^4329*12500000000000^3305 ≤ 1624277498431^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105656347 10000000000 1624277498431 12500000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245117371/10000000000 : ℝ)^4329 ≤ (42946320726199/100000000000000 : ℝ)^3305 := by
    have hnat : (5245117371 : ℕ)^4329*100000000000000^3305 ≤ 42946320726199^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245117371 10000000000 42946320726199 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267429709/500000000 : ℝ), (-2105656347/10000000000 : ℝ), (5245117371/10000000000 : ℝ)] ![(44059459282903/100000000000000 : ℝ), (1624277498431/12500000000000 : ℝ), (42946320726199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267429709/500000000 : ℝ)|^4329 ≤ (44059459282903/100000000000000 : ℝ)^3305
        have hw : |(267429709/500000000 : ℝ)|=(267429709/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2105656347/10000000000 : ℝ)|^4329 ≤ (1624277498431/12500000000000 : ℝ)^3305
        have hw : |(-2105656347/10000000000 : ℝ)|=(2105656347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245117371/10000000000 : ℝ)|^4329 ≤ (42946320726199/100000000000000 : ℝ)^3305
        have hw : |(5245117371/10000000000 : ℝ)|=(5245117371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s5_2 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668574279/1250000000 : ℝ)*x 0 + (2622558697/5000000000 : ℝ)*x 1 + (-421131249/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668574279/1250000000 : ℝ)^4329 ≤ (1762378393759/4000000000000 : ℝ)^3305 := by
    have hnat : (668574279 : ℕ)^4329*4000000000000^3305 ≤ 1762378393759^3305*1250000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668574279 1250000000 1762378393759 4000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622558697/5000000000 : ℝ)^4329 ≤ (10736580243217/25000000000000 : ℝ)^3305 := by
    have hnat : (2622558697 : ℕ)^4329*25000000000000^3305 ≤ 10736580243217^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622558697 5000000000 10736580243217 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (421131249/2000000000 : ℝ)^4329 ≤ (1299421916297/10000000000000 : ℝ)^3305 := by
    have hnat : (421131249 : ℕ)^4329*10000000000000^3305 ≤ 1299421916297^3305*2000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421131249 2000000000 1299421916297 10000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668574279/1250000000 : ℝ), (2622558697/5000000000 : ℝ), (-421131249/2000000000 : ℝ)] ![(1762378393759/4000000000000 : ℝ), (10736580243217/25000000000000 : ℝ), (1299421916297/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668574279/1250000000 : ℝ)|^4329 ≤ (1762378393759/4000000000000 : ℝ)^3305
        have hw : |(668574279/1250000000 : ℝ)|=(668574279/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622558697/5000000000 : ℝ)|^4329 ≤ (10736580243217/25000000000000 : ℝ)^3305
        have hw : |(2622558697/5000000000 : ℝ)|=(2622558697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-421131249/2000000000 : ℝ)|^4329 ≤ (1299421916297/10000000000000 : ℝ)^3305
        have hw : |(-421131249/2000000000 : ℝ)|=(421131249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s5_3 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2159793657/5000000000 : ℝ)*x 0 + (165870193/400000000 : ℝ)*x 1 + (4499053443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2159793657/5000000000 : ℝ)^4329 ≤ (33303511253771/100000000000000 : ℝ)^3305 := by
    have hnat : (2159793657 : ℕ)^4329*100000000000000^3305 ≤ 33303511253771^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2159793657 5000000000 33303511253771 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (165870193/400000000 : ℝ)^4329 ≤ (31569054053/100000000000 : ℝ)^3305 := by
    have hnat : (165870193 : ℕ)^4329*100000000000^3305 ≤ 31569054053^3305*400000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165870193 400000000 31569054053 100000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4499053443/10000000000 : ℝ)^4329 ≤ (8781858669993/25000000000000 : ℝ)^3305 := by
    have hnat : (4499053443 : ℕ)^4329*25000000000000^3305 ≤ 8781858669993^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499053443 10000000000 8781858669993 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2159793657/5000000000 : ℝ), (165870193/400000000 : ℝ), (4499053443/10000000000 : ℝ)] ![(33303511253771/100000000000000 : ℝ), (31569054053/100000000000 : ℝ), (8781858669993/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2159793657/5000000000 : ℝ)|^4329 ≤ (33303511253771/100000000000000 : ℝ)^3305
        have hw : |(2159793657/5000000000 : ℝ)|=(2159793657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(165870193/400000000 : ℝ)|^4329 ≤ (31569054053/100000000000 : ℝ)^3305
        have hw : |(165870193/400000000 : ℝ)|=(165870193/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4499053443/10000000000 : ℝ)|^4329 ≤ (8781858669993/25000000000000 : ℝ)^3305
        have hw : |(4499053443/10000000000 : ℝ)|=(4499053443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s5_4 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2020849457/10000000000 : ℝ)*x 0 + (5245716581/10000000000 : ℝ)*x 1 + (5411018137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2020849457/10000000000 : ℝ)^4329 ≤ (1539129181787/12500000000000 : ℝ)^3305 := by
    have hnat : (2020849457 : ℕ)^4329*12500000000000^3305 ≤ 1539129181787^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020849457 10000000000 1539129181787 12500000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245716581/10000000000 : ℝ)^4329 ≤ (42952747212891/100000000000000 : ℝ)^3305 := by
    have hnat : (5245716581 : ℕ)^4329*100000000000000^3305 ≤ 42952747212891^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245716581 10000000000 42952747212891 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411018137/10000000000 : ℝ)^4329 ≤ (22367109660981/50000000000000 : ℝ)^3305 := by
    have hnat : (5411018137 : ℕ)^4329*50000000000000^3305 ≤ 22367109660981^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411018137 10000000000 22367109660981 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2020849457/10000000000 : ℝ), (5245716581/10000000000 : ℝ), (5411018137/10000000000 : ℝ)] ![(1539129181787/12500000000000 : ℝ), (42952747212891/100000000000000 : ℝ), (22367109660981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2020849457/10000000000 : ℝ)|^4329 ≤ (1539129181787/12500000000000 : ℝ)^3305
        have hw : |(-2020849457/10000000000 : ℝ)|=(2020849457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245716581/10000000000 : ℝ)|^4329 ≤ (42952747212891/100000000000000 : ℝ)^3305
        have hw : |(5245716581/10000000000 : ℝ)|=(5245716581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411018137/10000000000 : ℝ)|^4329 ≤ (22367109660981/50000000000000 : ℝ)^3305
        have hw : |(5411018137/10000000000 : ℝ)|=(5411018137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s5_5 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652788307/5000000000 : ℝ)*x 0 + (-1939755537/10000000000 : ℝ)*x 1 + (84547153/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652788307/5000000000 : ℝ)^4329 ≤ (5449485667893/12500000000000 : ℝ)^3305 := by
    have hnat : (2652788307 : ℕ)^4329*12500000000000^3305 ≤ 5449485667893^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652788307 5000000000 5449485667893 12500000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1939755537/10000000000 : ℝ)^4329 ≤ (583494952941/5000000000000 : ℝ)^3305 := by
    have hnat : (1939755537 : ℕ)^4329*5000000000000^3305 ≤ 583494952941^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1939755537 10000000000 583494952941 5000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84547153/156250000 : ℝ)^4329 ≤ (22367107793027/50000000000000 : ℝ)^3305 := by
    have hnat : (84547153 : ℕ)^4329*50000000000000^3305 ≤ 22367107793027^3305*156250000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84547153 156250000 22367107793027 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652788307/5000000000 : ℝ), (-1939755537/10000000000 : ℝ), (84547153/156250000 : ℝ)] ![(5449485667893/12500000000000 : ℝ), (583494952941/5000000000000 : ℝ), (22367107793027/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652788307/5000000000 : ℝ)|^4329 ≤ (5449485667893/12500000000000 : ℝ)^3305
        have hw : |(2652788307/5000000000 : ℝ)|=(2652788307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1939755537/10000000000 : ℝ)|^4329 ≤ (583494952941/5000000000000 : ℝ)^3305
        have hw : |(-1939755537/10000000000 : ℝ)|=(1939755537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84547153/156250000 : ℝ)|^4329 ≤ (22367107793027/50000000000000 : ℝ)^3305
        have hw : |(84547153/156250000 : ℝ)|=(84547153/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s5_6 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305577077/10000000000 : ℝ)*x 0 + (2705508599/5000000000 : ℝ)*x 1 + (-1939755721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305577077/10000000000 : ℝ)^4329 ≤ (10898972581591/25000000000000 : ℝ)^3305 := by
    have hnat : (5305577077 : ℕ)^4329*25000000000000^3305 ≤ 10898972581591^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305577077 10000000000 10898972581591 25000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705508599/5000000000 : ℝ)^4329 ≤ (44734209153797/100000000000000 : ℝ)^3305 := by
    have hnat : (2705508599 : ℕ)^4329*100000000000000^3305 ≤ 44734209153797^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705508599 5000000000 44734209153797 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1939755721/10000000000 : ℝ)^4329 ≤ (11669900508773/100000000000000 : ℝ)^3305 := by
    have hnat : (1939755721 : ℕ)^4329*100000000000000^3305 ≤ 11669900508773^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1939755721 10000000000 11669900508773 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305577077/10000000000 : ℝ), (2705508599/5000000000 : ℝ), (-1939755721/10000000000 : ℝ)] ![(10898972581591/25000000000000 : ℝ), (44734209153797/100000000000000 : ℝ), (11669900508773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305577077/10000000000 : ℝ)|^4329 ≤ (10898972581591/25000000000000 : ℝ)^3305
        have hw : |(5305577077/10000000000 : ℝ)|=(5305577077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705508599/5000000000 : ℝ)|^4329 ≤ (44734209153797/100000000000000 : ℝ)^3305
        have hw : |(2705508599/5000000000 : ℝ)|=(2705508599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1939755721/10000000000 : ℝ)|^4329 ≤ (11669900508773/100000000000000 : ℝ)^3305
        have hw : |(-1939755721/10000000000 : ℝ)|=(1939755721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1369_s5_7 (p : ℝ) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4319613143/10000000000 : ℝ)*x 0 + (4497784771/10000000000 : ℝ)*x 1 + (2074014841/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319613143/10000000000 : ℝ)^4329 ≤ (6660754418477/20000000000000 : ℝ)^3305 := by
    have hnat : (4319613143 : ℕ)^4329*20000000000000^3305 ≤ 6660754418477^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319613143 10000000000 6660754418477 20000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4497784771/10000000000 : ℝ)^4329 ≤ (35114460742927/100000000000000 : ℝ)^3305 := by
    have hnat : (4497784771 : ℕ)^4329*100000000000000^3305 ≤ 35114460742927^3305*10000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4497784771 10000000000 35114460742927 100000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2074014841/5000000000 : ℝ)^4329 ≤ (15790883576851/50000000000000 : ℝ)^3305 := by
    have hnat : (2074014841 : ℕ)^4329*50000000000000^3305 ≤ 15790883576851^3305*5000000000^4329 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074014841 5000000000 15790883576851 50000000000000 4329 3305 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4329/1024 : ℝ)) 4329 3305 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319613143/10000000000 : ℝ), (4497784771/10000000000 : ℝ), (2074014841/5000000000 : ℝ)] ![(6660754418477/20000000000000 : ℝ), (35114460742927/100000000000000 : ℝ), (15790883576851/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319613143/10000000000 : ℝ)|^4329 ≤ (6660754418477/20000000000000 : ℝ)^3305
        have hw : |(4319613143/10000000000 : ℝ)|=(4319613143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4497784771/10000000000 : ℝ)|^4329 ≤ (35114460742927/100000000000000 : ℝ)^3305
        have hw : |(4497784771/10000000000 : ℝ)|=(4497784771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2074014841/5000000000 : ℝ)|^4329 ≤ (15790883576851/50000000000000 : ℝ)^3305
        have hw : |(2074014841/5000000000 : ℝ)|=(2074014841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1369_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77896747/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (923/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11169/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2241/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1473/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (923/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11169/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (923/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11169/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (923/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11169/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (923/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11169/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (923/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11169/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (923/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11169/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11169/100000 : ℝ) ^ (541/128 : ℝ) ≤ (9470499850189009/100000000000000000000 : ℝ) := by
    have hpowers : (11169/100000 : ℝ)^541 ≤ (9470499850189009/100000000000000000000 : ℝ)^128 := by
      have hnat : (11169 : ℕ)^541*100000000000000000000^128 ≤ 9470499850189009^128*100000^541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11169 100000 9470499850189009 100000000000000000000 541 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11169/100000 : ℝ)) (X := (9470499850189009/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hpowhi : (923/6250 : ℝ) ^ (541/128 : ℝ) ≤ (30837998195294697/100000000000000000000 : ℝ) := by
    have hpowers : (923/6250 : ℝ)^541 ≤ (30837998195294697/100000000000000000000 : ℝ)^128 := by
      have hnat : (923 : ℕ)^541*100000000000000000000^128 ≤ 30837998195294697^128*6250^541 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        923 6250 30837998195294697 100000000000000000000 541 128 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (923/6250 : ℝ)) (X := (30837998195294697/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009470499850189009/50000000000000000000 : ℝ) ≤ (1000044810955613/1000000000000000 : ℝ) ^ (541/128 : ℝ) := by
    have hpowers : (50009470499850189009/50000000000000000000 : ℝ)^128 ≤ (1000044810955613/1000000000000000 : ℝ)^541 := by
      have hnat : (50009470499850189009 : ℕ)^128*1000000000000000^541 ≤ 1000044810955613^541*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009470499850189009 50000000000000000000 1000044810955613 1000000000000000 128 541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000044810955613/1000000000000000 : ℝ)) (X := (50009470499850189009/50000000000000000000 : ℝ)) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020154249022741853/50000000000000000000 : ℝ) ≤ (2000190709578951/2000000000000000 : ℝ) ^ (541/128 : ℝ) := by
    have hpowers : (50020154249022741853/50000000000000000000 : ℝ)^128 ≤ (2000190709578951/2000000000000000 : ℝ)^541 := by
      have hnat : (50020154249022741853 : ℕ)^128*2000000000000000^541 ≤ 2000190709578951^541*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020154249022741853 50000000000000000000 2000190709578951 2000000000000000 128 541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000190709578951/2000000000000000 : ℝ)) (X := (50020154249022741853/50000000000000000000 : ℝ)) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030837998195294697/50000000000000000000 : ℝ) ≤ (500072949311669/500000000000000 : ℝ) ^ (541/128 : ℝ) := by
    have hpowers : (50030837998195294697/50000000000000000000 : ℝ)^128 ≤ (500072949311669/500000000000000 : ℝ)^541 := by
      have hnat : (50030837998195294697 : ℕ)^128*500000000000000^541 ≤ 500072949311669^541*50000000000000000000^128 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030837998195294697 50000000000000000000 500072949311669 500000000000000 128 541 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500072949311669/500000000000000 : ℝ)) (X := (50030837998195294697/50000000000000000000 : ℝ)) (by norm_num) 541 128 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9470499850189009/100000000000000000000 : ℝ) ≤ ((1799016113234215331/1799500000000000000 : ℝ)+2*(4043506709/2879200000000 : ℝ)*(11169/100000 : ℝ))^(541/128 : ℝ) := by
    rw [show (1799016113234215331/1799500000000000000 : ℝ)+2*(4043506709/2879200000000 : ℝ)*(11169/100000 : ℝ)=(1000044810955613/1000000000000000 : ℝ) by norm_num, show 1+2*(9470499850189009/100000000000000000000 : ℝ)=(50009470499850189009/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30837998195294697/100000000000000000000 : ℝ)+(9470499850189009/100000000000000000000 : ℝ) ≤ ((1799016113234215331/1799500000000000000 : ℝ)+(4043506709/2879200000000 : ℝ)*((923/6250 : ℝ)+(11169/100000 : ℝ)))^(541/128 : ℝ) := by
    rw [show (1799016113234215331/1799500000000000000 : ℝ)+(4043506709/2879200000000 : ℝ)*((923/6250 : ℝ)+(11169/100000 : ℝ))=(2000190709578951/2000000000000000 : ℝ) by norm_num, show 1+(30837998195294697/100000000000000000000 : ℝ)+(9470499850189009/100000000000000000000 : ℝ)=(50020154249022741853/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30837998195294697/100000000000000000000 : ℝ) ≤ ((1799016113234215331/1799500000000000000 : ℝ)+2*(4043506709/2879200000000 : ℝ)*(923/6250 : ℝ))^(541/128 : ℝ) := by
    rw [show (1799016113234215331/1799500000000000000 : ℝ)+2*(4043506709/2879200000000 : ℝ)*(923/6250 : ℝ)=(500072949311669/500000000000000 : ℝ) by norm_num, show 1+2*(30837998195294697/100000000000000000000 : ℝ)=(50030837998195294697/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1799016113234215331/1799500000000000000 : ℝ)*(X 1 0+X 2 0)+(4043506709/2879200000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (541/128 : ℝ)) (lo := (11169/100000 : ℝ)) (hi := (923/6250 : ℝ)) (c := (1799016113234215331/1799500000000000000 : ℝ)) (alpha := (4043506709/2879200000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1799016113234215331/1799500000000000000 : ℝ)*(X 0 1+X 2 1)+(4043506709/2879200000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (541/128 : ℝ)) (lo := (11169/100000 : ℝ)) (hi := (923/6250 : ℝ)) (c := (1799016113234215331/1799500000000000000 : ℝ)) (alpha := (4043506709/2879200000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1799016113234215331/1799500000000000000 : ℝ)*(X 0 2+X 1 2)+(4043506709/2879200000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (541/128 : ℝ)) (lo := (11169/100000 : ℝ)) (hi := (923/6250 : ℝ)) (c := (1799016113234215331/1799500000000000000 : ℝ)) (alpha := (4043506709/2879200000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1010418599/5000000000 : ℝ)*X 0 0+(2705810297/5000000000 : ℝ)*X 0 1+(1049023481/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((267429709/500000000 : ℝ)*X 1 0+(-2105656347/10000000000 : ℝ)*X 1 1+(5245117371/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668574279/1250000000 : ℝ)*X 2 0+(2622558697/5000000000 : ℝ)*X 2 1+(-421131249/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2159793657/5000000000 : ℝ)*X 0 0+(165870193/400000000 : ℝ)*X 0 1+(4499053443/10000000000 : ℝ)*X 0 2+(2159793657/5000000000 : ℝ)*X 1 0+(165870193/400000000 : ℝ)*X 1 1+(4499053443/10000000000 : ℝ)*X 1 2+(2159793657/5000000000 : ℝ)*X 2 0+(165870193/400000000 : ℝ)*X 2 1+(4499053443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2020849457/10000000000 : ℝ)*X 0 0+(5245716581/10000000000 : ℝ)*X 0 1+(5411018137/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652788307/5000000000 : ℝ)*X 1 0+(-1939755537/10000000000 : ℝ)*X 1 1+(84547153/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305577077/10000000000 : ℝ)*X 2 0+(2705508599/5000000000 : ℝ)*X 2 1+(-1939755721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4319613143/10000000000 : ℝ)*X 0 0+(4497784771/10000000000 : ℝ)*X 0 1+(2074014841/5000000000 : ℝ)*X 0 2+(4319613143/10000000000 : ℝ)*X 1 0+(4497784771/10000000000 : ℝ)*X 1 1+(2074014841/5000000000 : ℝ)*X 1 2+(4319613143/10000000000 : ℝ)*X 2 0+(4497784771/10000000000 : ℝ)*X 2 1+(2074014841/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1369_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (437544995159298070938657/71980000000000000000000000000 : ℝ) := by norm_num
    linear_combination (51410631/5000000000000 : ℝ)*(base19) + (209461981/20000000000000 : ℝ)*(base23) + (4203301/20000000000000 : ℝ)*(lower2) + (2029853/5000000000000 : ℝ)*(upper3) + (7340259/5000000000000 : ℝ)*(upper5) + (7075565526409/160000000000 : ℝ)*(major0) + (7075565526409/160000000000 : ℝ)*(major1) + (7075565526409/160000000000 : ℝ)*(major2) + (1201182315210537/20000000000000 : ℝ)*(sp0) + (1501484084878891/25000000000000 : ℝ)*(sp1) + (3002968160209139/50000000000000 : ℝ)*(sp2) + (1419255373887479/50000000000000 : ℝ)*(sp3) + (12895837749/50000000000000 : ℝ)*(sp4) + (8589884691/100000000000000 : ℝ)*(sp7) + (2838519337659649/100000000000000 : ℝ)*(f.failure) + (6005937367728183/100000000000000 : ℝ)*(f.sum) + (3582205011933/1799500000000000000000000000 : ℝ)*base66 + (2226654663103501/287920000000000000000000000000 : ℝ)*base68 + (1423193163650061/287920000000000000000000000000 : ℝ)*base70 + (113111725072979/287920000000000000000000000000 : ℝ)*base71 + (1177412916341/449875000000000000000000000 : ℝ)*base73 + (5993713728626621/287920000000000000000000000000 : ℝ)*base76 + (1588021839616941/287920000000000000000000000000 : ℝ)*base78 + (1733822086631181/287920000000000000000000000000 : ℝ)*base80 + (11588074579929/3599000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (261803/5000000000000000000000 : ℝ)*base89 + (261803/5000000000000000000000 : ℝ)*base91 + (261803/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17891433728326780233/89975000000000000000000000 : ℝ) := by norm_num
    linear_combination (193396833/12500000000000 : ℝ)*(base19) + (2097106723/100000000000000 : ℝ)*(base23) + (50011921/100000000000000 : ℝ)*(upper2) + (51823811/25000000000000 : ℝ)*(upper5) + (222717837497359/5000000000000 : ℝ)*(major0) + (222717837497359/5000000000000 : ℝ)*(major1) + (222717837497359/5000000000000 : ℝ)*(major2) + (5926804119/100000000000000 : ℝ)*(sp0) + (36142861143/100000000000000 : ℝ)*(sp1) + (13615668209/50000000000000 : ℝ)*(sp2) + (378097866769963/6250000000000 : ℝ)*(sp4) + (6049534105087721/100000000000000 : ℝ)*(sp5) + (3024771233340193/50000000000000 : ℝ)*(sp6) + (285914169814253/10000000000000 : ℝ)*(sp7) + (285914169814253/10000000000000 : ℝ)*(f.failure) + (6049571795123527/100000000000000 : ℝ)*(f.sum) + (2278201065241/449875000000000000000000000 : ℝ)*base66 + (18157925684095829/8997500000000000000000000000000 : ℝ)*base67 + (20548307821563329/8997500000000000000000000000000 : ℝ)*base69 + (41285271468754171/8997500000000000000000000000000 : ℝ)*base72 + (1013396326217/899750000000000000000000000 : ℝ)*base74 + (14112338491951671/8997500000000000000000000000000 : ℝ)*base76 + (115598757474094171/8997500000000000000000000000000 : ℝ)*base78 + (14571500716060829/8997500000000000000000000000000 : ℝ)*base79 + (1538519139039/899750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2934991/500000000000000000000 : ℝ)*base89 + (2934991/500000000000000000000 : ℝ)*base91 + (2934991/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1369_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77896747/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (923/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11169/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2241/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1369_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1369_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77896747/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16001/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10023/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2241/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1369_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1369_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1369_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (541/128 : ℝ) ≤ p) (hpb : p ≤ (4329/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77896747/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16001/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10023/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2241/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1473/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1369_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
