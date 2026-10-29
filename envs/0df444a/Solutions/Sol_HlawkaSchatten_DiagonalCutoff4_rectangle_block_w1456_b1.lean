-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1456_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:01:07.553593+00:00
-- url     : https://prove2.me/submissions/07571366-a575-4457-bbd8-ac057385f7d1

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
theorem support_rectangle_w1456_s3_0 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-121783197/625000000 : ℝ)*x 0 + (5414643001/10000000000 : ℝ)*x 1 + (5240256727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (121783197/625000000 : ℝ)^69 ≤ (74329190323/625000000000 : ℝ)^53 := by
    have hnat : (121783197 : ℕ)^69*625000000000^53 ≤ 74329190323^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      121783197 625000000 74329190323 625000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414643001/10000000000 : ℝ)^69 ≤ (44992287887217/100000000000000 : ℝ)^53 := by
    have hnat : (5414643001 : ℕ)^69*100000000000000^53 ≤ 44992287887217^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414643001 10000000000 44992287887217 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240256727/10000000000 : ℝ)^69 ≤ (43115041646649/100000000000000 : ℝ)^53 := by
    have hnat : (5240256727 : ℕ)^69*100000000000000^53 ≤ 43115041646649^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240256727 10000000000 43115041646649 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-121783197/625000000 : ℝ), (5414643001/10000000000 : ℝ), (5240256727/10000000000 : ℝ)] ![(74329190323/625000000000 : ℝ), (44992287887217/100000000000000 : ℝ), (43115041646649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-121783197/625000000 : ℝ)|^69 ≤ (74329190323/625000000000 : ℝ)^53
        have hw : |(-121783197/625000000 : ℝ)|=(121783197/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414643001/10000000000 : ℝ)|^69 ≤ (44992287887217/100000000000000 : ℝ)^53
        have hw : |(5414643001/10000000000 : ℝ)|=(5414643001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240256727/10000000000 : ℝ)|^69 ≤ (43115041646649/100000000000000 : ℝ)^53
        have hw : |(5240256727/10000000000 : ℝ)|=(5240256727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s3_1 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5348770111/10000000000 : ℝ)*x 0 + (-509360319/2500000000 : ℝ)*x 1 + (1048051383/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348770111/10000000000 : ℝ)^69 ≤ (22140498149151/50000000000000 : ℝ)^53 := by
    have hnat : (5348770111 : ℕ)^69*50000000000000^53 ≤ 22140498149151^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348770111 10000000000 22140498149151 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (509360319/2500000000 : ℝ)^69 ≤ (252079200569/2000000000000 : ℝ)^53 := by
    have hnat : (509360319 : ℕ)^69*2000000000000^53 ≤ 252079200569^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      509360319 2500000000 252079200569 2000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048051383/2000000000 : ℝ)^69 ≤ (43115043660407/100000000000000 : ℝ)^53 := by
    have hnat : (1048051383 : ℕ)^69*100000000000000^53 ≤ 43115043660407^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048051383 2000000000 43115043660407 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348770111/10000000000 : ℝ), (-509360319/2500000000 : ℝ), (1048051383/2000000000 : ℝ)] ![(22140498149151/50000000000000 : ℝ), (252079200569/2000000000000 : ℝ), (43115043660407/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348770111/10000000000 : ℝ)|^69 ≤ (22140498149151/50000000000000 : ℝ)^53
        have hw : |(5348770111/10000000000 : ℝ)|=(5348770111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-509360319/2500000000 : ℝ)|^69 ≤ (252079200569/2000000000000 : ℝ)^53
        have hw : |(-509360319/2500000000 : ℝ)|=(509360319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048051383/2000000000 : ℝ)|^69 ≤ (43115043660407/100000000000000 : ℝ)^53
        have hw : |(1048051383/2000000000 : ℝ)|=(1048051383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s3_2 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5348769719/10000000000 : ℝ)*x 0 + (2620128379/5000000000 : ℝ)*x 1 + (-203744201/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348769719/10000000000 : ℝ)^69 ≤ (44280992073341/100000000000000 : ℝ)^53 := by
    have hnat : (5348769719 : ℕ)^69*100000000000000^53 ≤ 44280992073341^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348769719 10000000000 44280992073341 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620128379/5000000000 : ℝ)^69 ≤ (2694690123669/6250000000000 : ℝ)^53 := by
    have hnat : (2620128379 : ℕ)^69*6250000000000^53 ≤ 2694690123669^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620128379 5000000000 2694690123669 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (203744201/1000000000 : ℝ)^69 ≤ (6301982969931/50000000000000 : ℝ)^53 := by
    have hnat : (203744201 : ℕ)^69*50000000000000^53 ≤ 6301982969931^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      203744201 1000000000 6301982969931 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348769719/10000000000 : ℝ), (2620128379/5000000000 : ℝ), (-203744201/1000000000 : ℝ)] ![(44280992073341/100000000000000 : ℝ), (2694690123669/6250000000000 : ℝ), (6301982969931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348769719/10000000000 : ℝ)|^69 ≤ (44280992073341/100000000000000 : ℝ)^53
        have hw : |(5348769719/10000000000 : ℝ)|=(5348769719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620128379/5000000000 : ℝ)|^69 ≤ (2694690123669/6250000000000 : ℝ)^53
        have hw : |(2620128379/5000000000 : ℝ)|=(2620128379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-203744201/1000000000 : ℝ)|^69 ≤ (6301982969931/50000000000000 : ℝ)^53
        have hw : |(-203744201/1000000000 : ℝ)|=(203744201/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s3_3 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4297115101/10000000000 : ℝ)*x 0 + (4110373631/10000000000 : ℝ)*x 1 + (4491362333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4297115101/10000000000 : ℝ)^69 ≤ (33299519268003/100000000000000 : ℝ)^53 := by
    have hnat : (4297115101 : ℕ)^69*100000000000000^53 ≤ 33299519268003^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297115101 10000000000 33299519268003 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4110373631/10000000000 : ℝ)^69 ≤ (15714015224309/50000000000000 : ℝ)^53 := by
    have hnat : (4110373631 : ℕ)^69*50000000000000^53 ≤ 15714015224309^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4110373631 10000000000 15714015224309 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4491362333/10000000000 : ℝ)^69 ≤ (17636225132977/50000000000000 : ℝ)^53 := by
    have hnat : (4491362333 : ℕ)^69*50000000000000^53 ≤ 17636225132977^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491362333 10000000000 17636225132977 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4297115101/10000000000 : ℝ), (4110373631/10000000000 : ℝ), (4491362333/10000000000 : ℝ)] ![(33299519268003/100000000000000 : ℝ), (15714015224309/50000000000000 : ℝ), (17636225132977/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4297115101/10000000000 : ℝ)|^69 ≤ (33299519268003/100000000000000 : ℝ)^53
        have hw : |(4297115101/10000000000 : ℝ)|=(4297115101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4110373631/10000000000 : ℝ)|^69 ≤ (15714015224309/50000000000000 : ℝ)^53
        have hw : |(4110373631/10000000000 : ℝ)|=(4110373631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4491362333/10000000000 : ℝ)|^69 ≤ (17636225132977/50000000000000 : ℝ)^53
        have hw : |(4491362333/10000000000 : ℝ)|=(4491362333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s3_4 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-974272457/5000000000 : ℝ)*x 0 + (655118357/1250000000 : ℝ)*x 1 + (5413949523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (974272457/5000000000 : ℝ)^69 ≤ (1486597475477/12500000000000 : ℝ)^53 := by
    have hnat : (974272457 : ℕ)^69*12500000000000^53 ≤ 1486597475477^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974272457 5000000000 1486597475477 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655118357/1250000000 : ℝ)^69 ≤ (10780608524083/25000000000000 : ℝ)^53 := by
    have hnat : (655118357 : ℕ)^69*25000000000000^53 ≤ 10780608524083^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655118357 1250000000 10780608524083 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413949523/10000000000 : ℝ)^69 ≤ (11246196520589/25000000000000 : ℝ)^53 := by
    have hnat : (5413949523 : ℕ)^69*25000000000000^53 ≤ 11246196520589^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413949523 10000000000 11246196520589 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-974272457/5000000000 : ℝ), (655118357/1250000000 : ℝ), (5413949523/10000000000 : ℝ)] ![(1486597475477/12500000000000 : ℝ), (10780608524083/25000000000000 : ℝ), (11246196520589/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-974272457/5000000000 : ℝ)|^69 ≤ (1486597475477/12500000000000 : ℝ)^53
        have hw : |(-974272457/5000000000 : ℝ)|=(974272457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655118357/1250000000 : ℝ)|^69 ≤ (10780608524083/25000000000000 : ℝ)^53
        have hw : |(655118357/1250000000 : ℝ)|=(655118357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413949523/10000000000 : ℝ)|^69 ≤ (11246196520589/25000000000000 : ℝ)^53
        have hw : |(5413949523/10000000000 : ℝ)|=(5413949523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s3_5 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5303318059/10000000000 : ℝ)*x 0 + (-1863749261/10000000000 : ℝ)*x 1 + (5413949501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5303318059/10000000000 : ℝ)^69 ≤ (218958726909/500000000000 : ℝ)^53 := by
    have hnat : (5303318059 : ℕ)^69*500000000000^53 ≤ 218958726909^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303318059 10000000000 218958726909 500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1863749261/10000000000 : ℝ)^69 ≤ (11223468762163/100000000000000 : ℝ)^53 := by
    have hnat : (1863749261 : ℕ)^69*100000000000000^53 ≤ 11223468762163^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1863749261 10000000000 11223468762163 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413949501/10000000000 : ℝ)^69 ≤ (11246196461093/25000000000000 : ℝ)^53 := by
    have hnat : (5413949501 : ℕ)^69*25000000000000^53 ≤ 11246196461093^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413949501 10000000000 11246196461093 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5303318059/10000000000 : ℝ), (-1863749261/10000000000 : ℝ), (5413949501/10000000000 : ℝ)] ![(218958726909/500000000000 : ℝ), (11223468762163/100000000000000 : ℝ), (11246196461093/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5303318059/10000000000 : ℝ)|^69 ≤ (218958726909/500000000000 : ℝ)^53
        have hw : |(5303318059/10000000000 : ℝ)|=(5303318059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1863749261/10000000000 : ℝ)|^69 ≤ (11223468762163/100000000000000 : ℝ)^53
        have hw : |(-1863749261/10000000000 : ℝ)|=(1863749261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413949501/10000000000 : ℝ)|^69 ≤ (11246196461093/25000000000000 : ℝ)^53
        have hw : |(5413949501/10000000000 : ℝ)|=(5413949501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s3_6 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (10358041/19531250 : ℝ)*x 0 + (5413950331/10000000000 : ℝ)*x 1 + (-931874789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10358041/19531250 : ℝ)^69 ≤ (43791733911303/100000000000000 : ℝ)^53 := by
    have hnat : (10358041 : ℕ)^69*100000000000000^53 ≤ 43791733911303^53*19531250^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10358041 19531250 43791733911303 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413950331/10000000000 : ℝ)^69 ≤ (11246198705713/25000000000000 : ℝ)^53 := by
    have hnat : (5413950331 : ℕ)^69*25000000000000^53 ≤ 11246198705713^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413950331 10000000000 11246198705713 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (931874789/5000000000 : ℝ)^69 ≤ (175366738241/1562500000000 : ℝ)^53 := by
    have hnat : (931874789 : ℕ)^69*1562500000000^53 ≤ 175366738241^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931874789 5000000000 175366738241 1562500000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10358041/19531250 : ℝ), (5413950331/10000000000 : ℝ), (-931874789/5000000000 : ℝ)] ![(43791733911303/100000000000000 : ℝ), (11246198705713/25000000000000 : ℝ), (175366738241/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10358041/19531250 : ℝ)|^69 ≤ (43791733911303/100000000000000 : ℝ)^53
        have hw : |(10358041/19531250 : ℝ)|=(10358041/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413950331/10000000000 : ℝ)|^69 ≤ (11246198705713/25000000000000 : ℝ)^53
        have hw : |(5413950331/10000000000 : ℝ)|=(5413950331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-931874789/5000000000 : ℝ)|^69 ≤ (175366738241/1562500000000 : ℝ)^53
        have hw : |(-931874789/5000000000 : ℝ)|=(931874789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s3_7 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (859429203/2000000000 : ℝ)*x 0 + (2244928377/5000000000 : ℝ)*x 1 + (4111888549/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (859429203/2000000000 : ℝ)^69 ≤ (4162478893711/12500000000000 : ℝ)^53 := by
    have hnat : (859429203 : ℕ)^69*12500000000000^53 ≤ 4162478893711^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      859429203 2000000000 4162478893711 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244928377/5000000000 : ℝ)^69 ≤ (35257057653681/100000000000000 : ℝ)^53 := by
    have hnat : (2244928377 : ℕ)^69*100000000000000^53 ≤ 35257057653681^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244928377 5000000000 35257057653681 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4111888549/10000000000 : ℝ)^69 ≤ (31443111178777/100000000000000 : ℝ)^53 := by
    have hnat : (4111888549 : ℕ)^69*100000000000000^53 ≤ 31443111178777^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4111888549 10000000000 31443111178777 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(859429203/2000000000 : ℝ), (2244928377/5000000000 : ℝ), (4111888549/10000000000 : ℝ)] ![(4162478893711/12500000000000 : ℝ), (35257057653681/100000000000000 : ℝ), (31443111178777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(859429203/2000000000 : ℝ)|^69 ≤ (4162478893711/12500000000000 : ℝ)^53
        have hw : |(859429203/2000000000 : ℝ)|=(859429203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2244928377/5000000000 : ℝ)|^69 ≤ (35257057653681/100000000000000 : ℝ)^53
        have hw : |(2244928377/5000000000 : ℝ)|=(2244928377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4111888549/10000000000 : ℝ)|^69 ≤ (31443111178777/100000000000000 : ℝ)^53
        have hw : |(4111888549/10000000000 : ℝ)|=(4111888549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1456_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15923767/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (393/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10507/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (281/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7467/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (393/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10507/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (393/2500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10507/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (393/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10507/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (393/2500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10507/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (393/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10507/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (393/2500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10507/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (10507/100000 : ℝ) ^ (4415/1024 : ℝ) ≤ (755079419112393/12500000000000000000 : ℝ) := by
    have hpowers : (10507/100000 : ℝ)^4415 ≤ (755079419112393/12500000000000000000 : ℝ)^1024 := by
      have hnat : (10507 : ℕ)^4415*12500000000000000000^1024 ≤ 755079419112393^1024*100000^4415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10507 100000 755079419112393 12500000000000000000 4415 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10507/100000 : ℝ)) (X := (755079419112393/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (393/2500 : ℝ) ^ (4415/1024 : ℝ) ≤ (4289397688543693/12500000000000000000 : ℝ) := by
    have hpowers : (393/2500 : ℝ)^4415 ≤ (4289397688543693/12500000000000000000 : ℝ)^1024 := by
      have hnat : (393 : ℕ)^4415*12500000000000000000^1024 ≤ 4289397688543693^1024*2500^4415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        393 2500 4289397688543693 12500000000000000000 4415 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (393/2500 : ℝ)) (X := (4289397688543693/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250755079419112393/6250000000000000000 : ℝ) ≤ (2000056039172229/2000000000000000 : ℝ) ^ (4415/1024 : ℝ) := by
    have hpowers : (6250755079419112393/6250000000000000000 : ℝ)^1024 ≤ (2000056039172229/2000000000000000 : ℝ)^4415 := by
      have hnat : (6250755079419112393 : ℕ)^1024*2000000000000000^4415 ≤ 2000056039172229^4415*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250755079419112393 6250000000000000000 2000056039172229 2000000000000000 1024 4415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000056039172229/2000000000000000 : ℝ)) (X := (6250755079419112393/6250000000000000000 : ℝ)) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252522238553828043/6250000000000000000 : ℝ) ≤ (5000467926994063/5000000000000000 : ℝ) ^ (4415/1024 : ℝ) := by
    have hpowers : (6252522238553828043/6250000000000000000 : ℝ)^1024 ≤ (5000467926994063/5000000000000000 : ℝ)^4415 := by
      have hnat : (6252522238553828043 : ℕ)^1024*5000000000000000^4415 ≤ 5000467926994063^4415*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252522238553828043 6250000000000000000 5000467926994063 5000000000000000 1024 4415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000467926994063/5000000000000000 : ℝ)) (X := (6252522238553828043/6250000000000000000 : ℝ)) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254289397688543693/6250000000000000000 : ℝ) ≤ (10001591512115107/10000000000000000 : ℝ) ^ (4415/1024 : ℝ) := by
    have hpowers : (6254289397688543693/6250000000000000000 : ℝ)^1024 ≤ (10001591512115107/10000000000000000 : ℝ)^4415 := by
      have hnat : (6254289397688543693 : ℕ)^1024*10000000000000000^4415 ≤ 10001591512115107^4415*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254289397688543693 6250000000000000000 10001591512115107 10000000000000000 1024 4415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001591512115107/10000000000000000 : ℝ)) (X := (6254289397688543693/6250000000000000000 : ℝ)) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(755079419112393/12500000000000000000 : ℝ) ≤ ((4009052512395674627/4010000000000000000 : ℝ)+2*(50435240537/40100000000000 : ℝ)*(10507/100000 : ℝ))^(4415/1024 : ℝ) := by
    rw [show (4009052512395674627/4010000000000000000 : ℝ)+2*(50435240537/40100000000000 : ℝ)*(10507/100000 : ℝ)=(2000056039172229/2000000000000000 : ℝ) by norm_num, show 1+2*(755079419112393/12500000000000000000 : ℝ)=(6250755079419112393/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4289397688543693/12500000000000000000 : ℝ)+(755079419112393/12500000000000000000 : ℝ) ≤ ((4009052512395674627/4010000000000000000 : ℝ)+(50435240537/40100000000000 : ℝ)*((393/2500 : ℝ)+(10507/100000 : ℝ)))^(4415/1024 : ℝ) := by
    rw [show (4009052512395674627/4010000000000000000 : ℝ)+(50435240537/40100000000000 : ℝ)*((393/2500 : ℝ)+(10507/100000 : ℝ))=(5000467926994063/5000000000000000 : ℝ) by norm_num, show 1+(4289397688543693/12500000000000000000 : ℝ)+(755079419112393/12500000000000000000 : ℝ)=(6252522238553828043/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4289397688543693/12500000000000000000 : ℝ) ≤ ((4009052512395674627/4010000000000000000 : ℝ)+2*(50435240537/40100000000000 : ℝ)*(393/2500 : ℝ))^(4415/1024 : ℝ) := by
    rw [show (4009052512395674627/4010000000000000000 : ℝ)+2*(50435240537/40100000000000 : ℝ)*(393/2500 : ℝ)=(10001591512115107/10000000000000000 : ℝ) by norm_num, show 1+2*(4289397688543693/12500000000000000000 : ℝ)=(6254289397688543693/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4009052512395674627/4010000000000000000 : ℝ)*(X 1 0+X 2 0)+(50435240537/40100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4415/1024 : ℝ)) (lo := (10507/100000 : ℝ)) (hi := (393/2500 : ℝ)) (c := (4009052512395674627/4010000000000000000 : ℝ)) (alpha := (50435240537/40100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4009052512395674627/4010000000000000000 : ℝ)*(X 0 1+X 2 1)+(50435240537/40100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4415/1024 : ℝ)) (lo := (10507/100000 : ℝ)) (hi := (393/2500 : ℝ)) (c := (4009052512395674627/4010000000000000000 : ℝ)) (alpha := (50435240537/40100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4009052512395674627/4010000000000000000 : ℝ)*(X 0 2+X 1 2)+(50435240537/40100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4415/1024 : ℝ)) (lo := (10507/100000 : ℝ)) (hi := (393/2500 : ℝ)) (c := (4009052512395674627/4010000000000000000 : ℝ)) (alpha := (50435240537/40100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-121783197/625000000 : ℝ)*X 0 0+(5414643001/10000000000 : ℝ)*X 0 1+(5240256727/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348770111/10000000000 : ℝ)*X 1 0+(-509360319/2500000000 : ℝ)*X 1 1+(1048051383/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348769719/10000000000 : ℝ)*X 2 0+(2620128379/5000000000 : ℝ)*X 2 1+(-203744201/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4297115101/10000000000 : ℝ)*X 0 0+(4110373631/10000000000 : ℝ)*X 0 1+(4491362333/10000000000 : ℝ)*X 0 2+(4297115101/10000000000 : ℝ)*X 1 0+(4110373631/10000000000 : ℝ)*X 1 1+(4491362333/10000000000 : ℝ)*X 1 2+(4297115101/10000000000 : ℝ)*X 2 0+(4110373631/10000000000 : ℝ)*X 2 1+(4491362333/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-974272457/5000000000 : ℝ)*X 0 0+(655118357/1250000000 : ℝ)*X 0 1+(5413949523/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5303318059/10000000000 : ℝ)*X 1 0+(-1863749261/10000000000 : ℝ)*X 1 1+(5413949501/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((10358041/19531250 : ℝ)*X 2 0+(5413950331/10000000000 : ℝ)*X 2 1+(-931874789/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((859429203/2000000000 : ℝ)*X 0 0+(2244928377/5000000000 : ℝ)*X 0 1+(4111888549/10000000000 : ℝ)*X 0 2+(859429203/2000000000 : ℝ)*X 1 0+(2244928377/5000000000 : ℝ)*X 1 1+(4111888549/10000000000 : ℝ)*X 1 2+(859429203/2000000000 : ℝ)*X 2 0+(2244928377/5000000000 : ℝ)*X 2 1+(4111888549/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1049347882251944029281376119/200500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (779377533/50000000000000 : ℝ)*(base19) + (274415119/20000000000000 : ℝ)*(base23) + (42013301/25000000000000 : ℝ)*(upper2) + (39718537/10000000000000 : ℝ)*(upper3) + (835923809092133/20000000000000 : ℝ)*(major0) + (835923809092133/20000000000000 : ℝ)*(major1) + (2089809522730333/50000000000000 : ℝ)*(major2) + (5734444088325247/100000000000000 : ℝ)*(sp0) + (5734468584193253/100000000000000 : ℝ)*(sp1) + (1146891857144871/20000000000000 : ℝ)*(sp2) + (1312378684231889/50000000000000 : ℝ)*(sp3) + (26054623073/100000000000000 : ℝ)*(sp4) + (948514837/10000000000000 : ℝ)*(sp6) + (10405054049/100000000000000 : ℝ)*(sp7) + (656191943379457/25000000000000 : ℝ)*(f.failure) + (5734470142948319/100000000000000 : ℝ)*(f.sum) + (6481340196277/4010000000000000000000000000 : ℝ)*base65 + (265435296553550609/80200000000000000000000000000000 : ℝ)*base68 + (1419017227925110791/200500000000000000000000000000000 : ℝ)*base69 + (34075790127049391/80200000000000000000000000000000 : ℝ)*base71 + (1997586810387/4010000000000000000000000000 : ℝ)*base73 + (1827884096651610791/200500000000000000000000000000000 : ℝ)*base75 + (173259300484090609/80200000000000000000000000000000 : ℝ)*base78 + (938118746729290609/80200000000000000000000000000000 : ℝ)*base80 + (74911321991/25062500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (3354519/250000000000000000000 : ℝ)*base89 + (3354519/250000000000000000000 : ℝ)*base91 + (854519/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (567948191133493741293453357/50125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (5175291/50000000000000 : ℝ)*(base8) + (526714769/100000000000000 : ℝ)*(base21) + (137564803/100000000000000 : ℝ)*(upper2) + (223375511/100000000000000 : ℝ)*(lower4) + (2106493100875003/50000000000000 : ℝ)*(major0) + (2106493100875003/50000000000000 : ℝ)*(major1) + (2106493100875003/50000000000000 : ℝ)*(major2) + (799755179/100000000000000 : ℝ)*(sp0) + (78050237/20000000000000 : ℝ)*(sp1) + (1122583783/50000000000000 : ℝ)*(sp2) + (1445062282846049/25000000000000 : ℝ)*(sp4) + (5780249551238771/100000000000000 : ℝ)*(sp5) + (5780247169607623/100000000000000 : ℝ)*(sp6) + (2645722084322137/100000000000000 : ℝ)*(sp7) + (2645722084322137/100000000000000 : ℝ)*(f.failure) + (5780249941489957/100000000000000 : ℝ)*(f.sum) + (10066662306293/2005000000000000000000000000 : ℝ)*base66 + (1161488583620248881/200500000000000000000000000000000 : ℝ)*base67 + (1864906021619748881/200500000000000000000000000000000 : ℝ)*base69 + (1218404954507248881/200500000000000000000000000000000 : ℝ)*base71 + (8208497085813/2005000000000000000000000000 : ℝ)*base74 + (1865162680667248881/200500000000000000000000000000000 : ℝ)*base75 + (6792525818165751119/200500000000000000000000000000000 : ℝ)*base78 + (1399132354277248881/200500000000000000000000000000000 : ℝ)*base79 + (989244867073/2005000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (2530079/1000000000000000000000 : ℝ)*base89 + (2530079/1000000000000000000000 : ℝ)*base91 + (2530079/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1456_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15923767/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (393/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10507/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (281/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7467/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1456_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1456_s4_0 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1949304549/10000000000 : ℝ)*x 0 + (675994857/1250000000 : ℝ)*x 1 + (1311607787/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1949304549/10000000000 : ℝ)^69 ≤ (11898816185571/100000000000000 : ℝ)^53 := by
    have hnat : (1949304549 : ℕ)^69*100000000000000^53 ≤ 11898816185571^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949304549 10000000000 11898816185571 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675994857/1250000000 : ℝ)^69 ≤ (2807499575039/6250000000000 : ℝ)^53 := by
    have hnat : (675994857 : ℕ)^69*6250000000000^53 ≤ 2807499575039^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675994857 1250000000 2807499575039 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311607787/2500000000 : ℝ)^69 ≤ (43181190590903/100000000000000 : ℝ)^53 := by
    have hnat : (1311607787 : ℕ)^69*100000000000000^53 ≤ 43181190590903^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311607787 2500000000 43181190590903 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1949304549/10000000000 : ℝ), (675994857/1250000000 : ℝ), (1311607787/2500000000 : ℝ)] ![(11898816185571/100000000000000 : ℝ), (2807499575039/6250000000000 : ℝ), (43181190590903/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1949304549/10000000000 : ℝ)|^69 ≤ (11898816185571/100000000000000 : ℝ)^53
        have hw : |(-1949304549/10000000000 : ℝ)|=(1949304549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675994857/1250000000 : ℝ)|^69 ≤ (2807499575039/6250000000000 : ℝ)^53
        have hw : |(675994857/1250000000 : ℝ)|=(675994857/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311607787/2500000000 : ℝ)|^69 ≤ (43181190590903/100000000000000 : ℝ)^53
        have hw : |(1311607787/2500000000 : ℝ)|=(1311607787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s4_1 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5347038599/10000000000 : ℝ)*x 0 + (-507885593/2500000000 : ℝ)*x 1 + (524643129/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347038599/10000000000 : ℝ)^69 ≤ (44262335038687/100000000000000 : ℝ)^53 := by
    have hnat : (5347038599 : ℕ)^69*100000000000000^53 ≤ 44262335038687^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347038599 10000000000 44262335038687 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (507885593/2500000000 : ℝ)^69 ≤ (12556472835103/100000000000000 : ℝ)^53 := by
    have hnat : (507885593 : ℕ)^69*100000000000000^53 ≤ 12556472835103^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507885593 2500000000 12556472835103 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524643129/1000000000 : ℝ)^69 ≤ (43181192112473/100000000000000 : ℝ)^53 := by
    have hnat : (524643129 : ℕ)^69*100000000000000^53 ≤ 43181192112473^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524643129 1000000000 43181192112473 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347038599/10000000000 : ℝ), (-507885593/2500000000 : ℝ), (524643129/1000000000 : ℝ)] ![(44262335038687/100000000000000 : ℝ), (12556472835103/100000000000000 : ℝ), (43181192112473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347038599/10000000000 : ℝ)|^69 ≤ (44262335038687/100000000000000 : ℝ)^53
        have hw : |(5347038599/10000000000 : ℝ)|=(5347038599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-507885593/2500000000 : ℝ)|^69 ≤ (12556472835103/100000000000000 : ℝ)^53
        have hw : |(-507885593/2500000000 : ℝ)|=(507885593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524643129/1000000000 : ℝ)|^69 ≤ (43181192112473/100000000000000 : ℝ)^53
        have hw : |(524643129/1000000000 : ℝ)|=(524643129/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s4_2 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5347038443/10000000000 : ℝ)*x 0 + (2623215727/5000000000 : ℝ)*x 1 + (-2031542363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347038443/10000000000 : ℝ)^69 ≤ (44262333357489/100000000000000 : ℝ)^53 := by
    have hnat : (5347038443 : ℕ)^69*100000000000000^53 ≤ 44262333357489^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347038443 10000000000 44262333357489 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623215727/5000000000 : ℝ)^69 ≤ (43181193869781/100000000000000 : ℝ)^53 := by
    have hnat : (2623215727 : ℕ)^69*100000000000000^53 ≤ 43181193869781^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623215727 5000000000 43181193869781 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2031542363/10000000000 : ℝ)^69 ≤ (12556472762683/100000000000000 : ℝ)^53 := by
    have hnat : (2031542363 : ℕ)^69*100000000000000^53 ≤ 12556472762683^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2031542363 10000000000 12556472762683 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347038443/10000000000 : ℝ), (2623215727/5000000000 : ℝ), (-2031542363/10000000000 : ℝ)] ![(44262333357489/100000000000000 : ℝ), (43181193869781/100000000000000 : ℝ), (12556472762683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347038443/10000000000 : ℝ)|^69 ≤ (44262333357489/100000000000000 : ℝ)^53
        have hw : |(5347038443/10000000000 : ℝ)|=(5347038443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623215727/5000000000 : ℝ)|^69 ≤ (43181193869781/100000000000000 : ℝ)^53
        have hw : |(2623215727/5000000000 : ℝ)|=(2623215727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2031542363/10000000000 : ℝ)|^69 ≤ (12556472762683/100000000000000 : ℝ)^53
        have hw : |(-2031542363/10000000000 : ℝ)|=(2031542363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s4_3 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4297590709/10000000000 : ℝ)*x 0 + (257772639/625000000 : ℝ)*x 1 + (111931503/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4297590709/10000000000 : ℝ)^69 ≤ (33304317603437/100000000000000 : ℝ)^53 := by
    have hnat : (4297590709 : ℕ)^69*100000000000000^53 ≤ 33304317603437^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297590709 10000000000 33304317603437 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (257772639/625000000 : ℝ)^69 ≤ (15783674023951/50000000000000 : ℝ)^53 := by
    have hnat : (257772639 : ℕ)^69*50000000000000^53 ≤ 15783674023951^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257772639 625000000 15783674023951 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (111931503/250000000 : ℝ)^69 ≤ (35128334332349/100000000000000 : ℝ)^53 := by
    have hnat : (111931503 : ℕ)^69*100000000000000^53 ≤ 35128334332349^53*250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111931503 250000000 35128334332349 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4297590709/10000000000 : ℝ), (257772639/625000000 : ℝ), (111931503/250000000 : ℝ)] ![(33304317603437/100000000000000 : ℝ), (15783674023951/50000000000000 : ℝ), (35128334332349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4297590709/10000000000 : ℝ)|^69 ≤ (33304317603437/100000000000000 : ℝ)^53
        have hw : |(4297590709/10000000000 : ℝ)|=(4297590709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(257772639/625000000 : ℝ)|^69 ≤ (15783674023951/50000000000000 : ℝ)^53
        have hw : |(257772639/625000000 : ℝ)|=(257772639/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(111931503/250000000 : ℝ)|^69 ≤ (35128334332349/100000000000000 : ℝ)^53
        have hw : |(111931503/250000000 : ℝ)|=(111931503/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s4_4 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1949316219/10000000000 : ℝ)*x 0 + (5247023119/10000000000 : ℝ)*x 1 + (5407363683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1949316219/10000000000 : ℝ)^69 ≤ (5949454462939/50000000000000 : ℝ)^53 := by
    have hnat : (1949316219 : ℕ)^69*50000000000000^53 ≤ 5949454462939^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949316219 10000000000 5949454462939 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247023119/10000000000 : ℝ)^69 ≤ (43187533838797/100000000000000 : ℝ)^53 := by
    have hnat : (5247023119 : ℕ)^69*100000000000000^53 ≤ 43187533838797^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247023119 10000000000 43187533838797 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407363683/10000000000 : ℝ)^69 ≤ (5614194651013/12500000000000 : ℝ)^53 := by
    have hnat : (5407363683 : ℕ)^69*12500000000000^53 ≤ 5614194651013^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407363683 10000000000 5614194651013 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1949316219/10000000000 : ℝ), (5247023119/10000000000 : ℝ), (5407363683/10000000000 : ℝ)] ![(5949454462939/50000000000000 : ℝ), (43187533838797/100000000000000 : ℝ), (5614194651013/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1949316219/10000000000 : ℝ)|^69 ≤ (5949454462939/50000000000000 : ℝ)^53
        have hw : |(-1949316219/10000000000 : ℝ)|=(1949316219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247023119/10000000000 : ℝ)|^69 ≤ (43187533838797/100000000000000 : ℝ)^53
        have hw : |(5247023119/10000000000 : ℝ)|=(5247023119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407363683/10000000000 : ℝ)|^69 ≤ (5614194651013/12500000000000 : ℝ)^53
        have hw : |(5407363683/10000000000 : ℝ)|=(5407363683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s4_5 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5304937567/10000000000 : ℝ)*x 0 + (-1870610031/10000000000 : ℝ)*x 1 + (5407363669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304937567/10000000000 : ℝ)^69 ≤ (21904578134791/50000000000000 : ℝ)^53 := by
    have hnat : (5304937567 : ℕ)^69*50000000000000^53 ≤ 21904578134791^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304937567 10000000000 21904578134791 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1870610031/10000000000 : ℝ)^69 ≤ (11277286661341/100000000000000 : ℝ)^53 := by
    have hnat : (1870610031 : ℕ)^69*100000000000000^53 ≤ 11277286661341^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870610031 10000000000 11277286661341 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407363669/10000000000 : ℝ)^69 ≤ (11228389264179/25000000000000 : ℝ)^53 := by
    have hnat : (5407363669 : ℕ)^69*25000000000000^53 ≤ 11228389264179^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407363669 10000000000 11228389264179 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304937567/10000000000 : ℝ), (-1870610031/10000000000 : ℝ), (5407363669/10000000000 : ℝ)] ![(21904578134791/50000000000000 : ℝ), (11277286661341/100000000000000 : ℝ), (11228389264179/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304937567/10000000000 : ℝ)|^69 ≤ (21904578134791/50000000000000 : ℝ)^53
        have hw : |(5304937567/10000000000 : ℝ)|=(5304937567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1870610031/10000000000 : ℝ)|^69 ≤ (11277286661341/100000000000000 : ℝ)^53
        have hw : |(-1870610031/10000000000 : ℝ)|=(1870610031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407363669/10000000000 : ℝ)|^69 ≤ (11228389264179/25000000000000 : ℝ)^53
        have hw : |(5407363669/10000000000 : ℝ)|=(5407363669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s4_6 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1326234409/2500000000 : ℝ)*x 0 + (5407363629/10000000000 : ℝ)*x 1 + (-1870609991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326234409/2500000000 : ℝ)^69 ≤ (5476144626427/12500000000000 : ℝ)^53 := by
    have hnat : (1326234409 : ℕ)^69*12500000000000^53 ≤ 5476144626427^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326234409 2500000000 5476144626427 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407363629/10000000000 : ℝ)^69 ≤ (44913556624177/100000000000000 : ℝ)^53 := by
    have hnat : (5407363629 : ℕ)^69*100000000000000^53 ≤ 44913556624177^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407363629 10000000000 44913556624177 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1870609991/10000000000 : ℝ)^69 ≤ (2819321586849/25000000000000 : ℝ)^53 := by
    have hnat : (1870609991 : ℕ)^69*25000000000000^53 ≤ 2819321586849^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870609991 10000000000 2819321586849 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326234409/2500000000 : ℝ), (5407363629/10000000000 : ℝ), (-1870609991/10000000000 : ℝ)] ![(5476144626427/12500000000000 : ℝ), (44913556624177/100000000000000 : ℝ), (2819321586849/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326234409/2500000000 : ℝ)|^69 ≤ (5476144626427/12500000000000 : ℝ)^53
        have hw : |(1326234409/2500000000 : ℝ)|=(1326234409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407363629/10000000000 : ℝ)|^69 ≤ (44913556624177/100000000000000 : ℝ)^53
        have hw : |(5407363629/10000000000 : ℝ)|=(5407363629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1870609991/10000000000 : ℝ)|^69 ≤ (2819321586849/25000000000000 : ℝ)^53
        have hw : |(-1870609991/10000000000 : ℝ)|=(1870609991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s4_7 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2148808027/5000000000 : ℝ)*x 0 + (4475966693/10000000000 : ℝ)*x 1 + (4125662327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148808027/5000000000 : ℝ)^69 ≤ (6660914661943/20000000000000 : ℝ)^53 := by
    have hnat : (2148808027 : ℕ)^69*20000000000000^53 ≤ 6660914661943^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148808027 5000000000 6660914661943 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4475966693/10000000000 : ℝ)^69 ≤ (8778780789417/25000000000000 : ℝ)^53 := by
    have hnat : (4475966693 : ℕ)^69*25000000000000^53 ≤ 8778780789417^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475966693 10000000000 8778780789417 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4125662327/10000000000 : ℝ)^69 ≤ (7895075877753/25000000000000 : ℝ)^53 := by
    have hnat : (4125662327 : ℕ)^69*25000000000000^53 ≤ 7895075877753^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4125662327 10000000000 7895075877753 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2148808027/5000000000 : ℝ), (4475966693/10000000000 : ℝ), (4125662327/10000000000 : ℝ)] ![(6660914661943/20000000000000 : ℝ), (8778780789417/25000000000000 : ℝ), (7895075877753/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2148808027/5000000000 : ℝ)|^69 ≤ (6660914661943/20000000000000 : ℝ)^53
        have hw : |(2148808027/5000000000 : ℝ)|=(2148808027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4475966693/10000000000 : ℝ)|^69 ≤ (8778780789417/25000000000000 : ℝ)^53
        have hw : |(4475966693/10000000000 : ℝ)|=(4475966693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4125662327/10000000000 : ℝ)|^69 ≤ (7895075877753/25000000000000 : ℝ)^53
        have hw : |(4125662327/10000000000 : ℝ)|=(4125662327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1456_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15923767/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7467/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (281/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (2843/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7397/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7467/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (281/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7467/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (281/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7467/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (281/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7467/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (281/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7467/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (281/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7467/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (281/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (281/2500 : ℝ) ^ (4415/1024 : ℝ) ≤ (4039491583134411/50000000000000000000 : ℝ) := by
    have hpowers : (281/2500 : ℝ)^4415 ≤ (4039491583134411/50000000000000000000 : ℝ)^1024 := by
      have hnat : (281 : ℕ)^4415*50000000000000000000^1024 ≤ 4039491583134411^1024*2500^4415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        281 2500 4039491583134411 50000000000000000000 4415 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (281/2500 : ℝ)) (X := (4039491583134411/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7467/50000 : ℝ) ^ (4415/1024 : ℝ) ≤ (6876716353159977/25000000000000000000 : ℝ) := by
    have hpowers : (7467/50000 : ℝ)^4415 ≤ (6876716353159977/25000000000000000000 : ℝ)^1024 := by
      have hnat : (7467 : ℕ)^4415*25000000000000000000^1024 ≤ 6876716353159977^1024*50000^4415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7467 50000 6876716353159977 25000000000000000000 4415 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7467/50000 : ℝ)) (X := (6876716353159977/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004039491583134411/25000000000000000000 : ℝ) ≤ (2000074947818481/2000000000000000 : ℝ) ^ (4415/1024 : ℝ) := by
    have hpowers : (25004039491583134411/25000000000000000000 : ℝ)^1024 ≤ (2000074947818481/2000000000000000 : ℝ)^4415 := by
      have hnat : (25004039491583134411 : ℕ)^1024*2000000000000000^4415 ≤ 2000074947818481^4415*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004039491583134411 25000000000000000000 2000074947818481 2000000000000000 1024 4415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000074947818481/2000000000000000 : ℝ)) (X := (25004039491583134411/25000000000000000000 : ℝ)) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003558584857890873/10000000000000000000 : ℝ) ≤ (1000082525322937/1000000000000000 : ℝ) ^ (4415/1024 : ℝ) := by
    have hpowers : (10003558584857890873/10000000000000000000 : ℝ)^1024 ≤ (1000082525322937/1000000000000000 : ℝ)^4415 := by
      have hnat : (10003558584857890873 : ℕ)^1024*1000000000000000^4415 ≤ 1000082525322937^4415*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003558584857890873 10000000000000000000 1000082525322937 1000000000000000 1024 4415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000082525322937/1000000000000000 : ℝ)) (X := (10003558584857890873/10000000000000000000 : ℝ)) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12506876716353159977/12500000000000000000 : ℝ) ≤ (2000255153473267/2000000000000000 : ℝ) ^ (4415/1024 : ℝ) := by
    have hpowers : (12506876716353159977/12500000000000000000 : ℝ)^1024 ≤ (2000255153473267/2000000000000000 : ℝ)^4415 := by
      have hnat : (12506876716353159977 : ℕ)^1024*2000000000000000^4415 ≤ 2000255153473267^4415*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506876716353159977 12500000000000000000 2000255153473267 2000000000000000 1024 4415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000255153473267/2000000000000000 : ℝ)) (X := (12506876716353159977/12500000000000000000 : ℝ)) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4039491583134411/50000000000000000000 : ℝ) ≤ ((3693125672840837087/3694000000000000000 : ℝ)+2*(90102827393/73880000000000 : ℝ)*(281/2500 : ℝ))^(4415/1024 : ℝ) := by
    rw [show (3693125672840837087/3694000000000000000 : ℝ)+2*(90102827393/73880000000000 : ℝ)*(281/2500 : ℝ)=(2000074947818481/2000000000000000 : ℝ) by norm_num, show 1+2*(4039491583134411/50000000000000000000 : ℝ)=(25004039491583134411/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6876716353159977/25000000000000000000 : ℝ)+(4039491583134411/50000000000000000000 : ℝ) ≤ ((3693125672840837087/3694000000000000000 : ℝ)+(90102827393/73880000000000 : ℝ)*((7467/50000 : ℝ)+(281/2500 : ℝ)))^(4415/1024 : ℝ) := by
    rw [show (3693125672840837087/3694000000000000000 : ℝ)+(90102827393/73880000000000 : ℝ)*((7467/50000 : ℝ)+(281/2500 : ℝ))=(1000082525322937/1000000000000000 : ℝ) by norm_num, show 1+(6876716353159977/25000000000000000000 : ℝ)+(4039491583134411/50000000000000000000 : ℝ)=(10003558584857890873/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6876716353159977/25000000000000000000 : ℝ) ≤ ((3693125672840837087/3694000000000000000 : ℝ)+2*(90102827393/73880000000000 : ℝ)*(7467/50000 : ℝ))^(4415/1024 : ℝ) := by
    rw [show (3693125672840837087/3694000000000000000 : ℝ)+2*(90102827393/73880000000000 : ℝ)*(7467/50000 : ℝ)=(2000255153473267/2000000000000000 : ℝ) by norm_num, show 1+2*(6876716353159977/25000000000000000000 : ℝ)=(12506876716353159977/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3693125672840837087/3694000000000000000 : ℝ)*(X 1 0+X 2 0)+(90102827393/73880000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4415/1024 : ℝ)) (lo := (281/2500 : ℝ)) (hi := (7467/50000 : ℝ)) (c := (3693125672840837087/3694000000000000000 : ℝ)) (alpha := (90102827393/73880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3693125672840837087/3694000000000000000 : ℝ)*(X 0 1+X 2 1)+(90102827393/73880000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4415/1024 : ℝ)) (lo := (281/2500 : ℝ)) (hi := (7467/50000 : ℝ)) (c := (3693125672840837087/3694000000000000000 : ℝ)) (alpha := (90102827393/73880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3693125672840837087/3694000000000000000 : ℝ)*(X 0 2+X 1 2)+(90102827393/73880000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4415/1024 : ℝ)) (lo := (281/2500 : ℝ)) (hi := (7467/50000 : ℝ)) (c := (3693125672840837087/3694000000000000000 : ℝ)) (alpha := (90102827393/73880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1949304549/10000000000 : ℝ)*X 0 0+(675994857/1250000000 : ℝ)*X 0 1+(1311607787/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347038599/10000000000 : ℝ)*X 1 0+(-507885593/2500000000 : ℝ)*X 1 1+(524643129/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347038443/10000000000 : ℝ)*X 2 0+(2623215727/5000000000 : ℝ)*X 2 1+(-2031542363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4297590709/10000000000 : ℝ)*X 0 0+(257772639/625000000 : ℝ)*X 0 1+(111931503/250000000 : ℝ)*X 0 2+(4297590709/10000000000 : ℝ)*X 1 0+(257772639/625000000 : ℝ)*X 1 1+(111931503/250000000 : ℝ)*X 1 2+(4297590709/10000000000 : ℝ)*X 2 0+(257772639/625000000 : ℝ)*X 2 1+(111931503/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1949316219/10000000000 : ℝ)*X 0 0+(5247023119/10000000000 : ℝ)*X 0 1+(5407363683/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304937567/10000000000 : ℝ)*X 1 0+(-1870610031/10000000000 : ℝ)*X 1 1+(5407363669/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326234409/2500000000 : ℝ)*X 2 0+(5407363629/10000000000 : ℝ)*X 2 1+(-1870609991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2148808027/5000000000 : ℝ)*X 0 0+(4475966693/10000000000 : ℝ)*X 0 1+(4125662327/10000000000 : ℝ)*X 0 2+(2148808027/5000000000 : ℝ)*X 1 0+(4475966693/10000000000 : ℝ)*X 1 1+(4125662327/10000000000 : ℝ)*X 1 2+(2148808027/5000000000 : ℝ)*X 2 0+(4475966693/10000000000 : ℝ)*X 2 1+(4125662327/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (551429796697046400722507673/92350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28235963/4000000000000 : ℝ)*(base19) + (193048741/50000000000000 : ℝ)*(base23) + (22711677/25000000000000 : ℝ)*(lower2) + (29835941/25000000000000 : ℝ)*(upper3) + (4106517/25000000000000 : ℝ)*(lower4) + (4512314008728507/100000000000000 : ℝ)*(major0) + (4512314008728507/100000000000000 : ℝ)*(major1) + (4512314008728507/100000000000000 : ℝ)*(major2) + (619091133626909/10000000000000 : ℝ)*(sp0) + (6190929527817997/100000000000000 : ℝ)*(sp1) + (619092984761959/10000000000000 : ℝ)*(sp2) + (113347532797319/4000000000000 : ℝ)*(sp3) + (9448723991/50000000000000 : ℝ)*(sp4) + (4632385381/50000000000000 : ℝ)*(sp7) + (2833697584703737/100000000000000 : ℝ)*(f.failure) + (386933139607317/6250000000000 : ℝ)*(f.sum) + (3646364750481/3694000000000000000000000000 : ℝ)*base65 + (459850823350689109/369400000000000000000000000000000 : ℝ)*base67 + (1998782365932289109/369400000000000000000000000000000 : ℝ)*base69 + (599267827567889109/369400000000000000000000000000000 : ℝ)*base71 + (4728914475657/3694000000000000000000000000 : ℝ)*base74 + (2090440441314689109/369400000000000000000000000000000 : ℝ)*base75 + (1456085654921910891/369400000000000000000000000000000 : ℝ)*base78 + (3014574323587889109/369400000000000000000000000000000 : ℝ)*base79 + (455557030859/147760000000000000000000000 : ℝ)*base81 + (2017279/1000000000000000000000 : ℝ)*base89 + (2017279/1000000000000000000000 : ℝ)*base91 + (2017279/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1198327981594129651408014003/184700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (236482123/25000000000000 : ℝ)*(base19) + (14721941/1250000000000 : ℝ)*(base23) + (48161253/50000000000000 : ℝ)*(upper3) + (34005351/50000000000000 : ℝ)*(lower4) + (78088853/50000000000000 : ℝ)*(upper5) + (4545693010155023/100000000000000 : ℝ)*(major0) + (4545693010155023/100000000000000 : ℝ)*(major1) + (4545693010155023/100000000000000 : ℝ)*(major2) + (20466772011/100000000000000 : ℝ)*(sp1) + (23302588919/100000000000000 : ℝ)*(sp2) + (6236726469883679/100000000000000 : ℝ)*(sp4) + (6236705057183177/100000000000000 : ℝ)*(sp5) + (155917549738487/2500000000000 : ℝ)*(sp6) + (2854659334160707/100000000000000 : ℝ)*(sp7) + (2854659334160707/100000000000000 : ℝ)*(f.failure) + (6236726469883679/100000000000000 : ℝ)*(f.sum) + (26333524216999/3694000000000000000000000000 : ℝ)*base66 + (1451221840020888001/369400000000000000000000000000000 : ℝ)*base67 + (392703113157288001/369400000000000000000000000000000 : ℝ)*base69 + (2797634090534711999/369400000000000000000000000000000 : ℝ)*base72 + (13452950668871/3694000000000000000000000000 : ℝ)*base73 + (8301270265355111999/369400000000000000000000000000000 : ℝ)*base76 + (2229171614995311999/369400000000000000000000000000000 : ℝ)*base78 + (739784253822111999/369400000000000000000000000000000 : ℝ)*base80 + (1334986639889/3694000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (8823269/1000000000000000000000 : ℝ)*base89 + (8823269/1000000000000000000000 : ℝ)*base91 + (8823269/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1456_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15923767/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7467/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (281/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2843/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7397/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1456_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1456_s5_0 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-487353953/2500000000 : ℝ)*x 0 + (5406968801/10000000000 : ℝ)*x 1 + (5247347739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (487353953/2500000000 : ℝ)^69 ≤ (11899700388171/100000000000000 : ℝ)^53 := by
    have hnat : (487353953 : ℕ)^69*100000000000000^53 ≤ 11899700388171^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487353953 2500000000 11899700388171 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406968801/10000000000 : ℝ)^69 ≤ (44909287210369/100000000000000 : ℝ)^53 := by
    have hnat : (5406968801 : ℕ)^69*100000000000000^53 ≤ 44909287210369^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406968801 10000000000 44909287210369 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247347739/10000000000 : ℝ)^69 ≤ (43191012386611/100000000000000 : ℝ)^53 := by
    have hnat : (5247347739 : ℕ)^69*100000000000000^53 ≤ 43191012386611^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247347739 10000000000 43191012386611 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-487353953/2500000000 : ℝ), (5406968801/10000000000 : ℝ), (5247347739/10000000000 : ℝ)] ![(11899700388171/100000000000000 : ℝ), (44909287210369/100000000000000 : ℝ), (43191012386611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-487353953/2500000000 : ℝ)|^69 ≤ (11899700388171/100000000000000 : ℝ)^53
        have hw : |(-487353953/2500000000 : ℝ)|=(487353953/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406968801/10000000000 : ℝ)|^69 ≤ (44909287210369/100000000000000 : ℝ)^53
        have hw : |(5406968801/10000000000 : ℝ)|=(5406968801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247347739/10000000000 : ℝ)|^69 ≤ (43191012386611/100000000000000 : ℝ)^53
        have hw : |(5247347739/10000000000 : ℝ)|=(5247347739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s5_1 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5346781831/10000000000 : ℝ)*x 0 + (-253833223/1250000000 : ℝ)*x 1 + (5247347739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346781831/10000000000 : ℝ)^69 ≤ (44259567893327/100000000000000 : ℝ)^53 := by
    have hnat : (5346781831 : ℕ)^69*100000000000000^53 ≤ 44259567893327^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346781831 10000000000 44259567893327 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (253833223/1250000000 : ℝ)^69 ≤ (1254941969957/10000000000000 : ℝ)^53 := by
    have hnat : (253833223 : ℕ)^69*10000000000000^53 ≤ 1254941969957^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253833223 1250000000 1254941969957 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247347739/10000000000 : ℝ)^69 ≤ (43191012386611/100000000000000 : ℝ)^53 := by
    have hnat : (5247347739 : ℕ)^69*100000000000000^53 ≤ 43191012386611^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247347739 10000000000 43191012386611 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346781831/10000000000 : ℝ), (-253833223/1250000000 : ℝ), (5247347739/10000000000 : ℝ)] ![(44259567893327/100000000000000 : ℝ), (1254941969957/10000000000000 : ℝ), (43191012386611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346781831/10000000000 : ℝ)|^69 ≤ (44259567893327/100000000000000 : ℝ)^53
        have hw : |(5346781831/10000000000 : ℝ)|=(5346781831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-253833223/1250000000 : ℝ)|^69 ≤ (1254941969957/10000000000000 : ℝ)^53
        have hw : |(-253833223/1250000000 : ℝ)|=(253833223/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247347739/10000000000 : ℝ)|^69 ≤ (43191012386611/100000000000000 : ℝ)^53
        have hw : |(5247347739/10000000000 : ℝ)|=(5247347739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s5_2 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5346781831/10000000000 : ℝ)*x 0 + (5247347739/10000000000 : ℝ)*x 1 + (-253833223/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346781831/10000000000 : ℝ)^69 ≤ (44259567893327/100000000000000 : ℝ)^53 := by
    have hnat : (5346781831 : ℕ)^69*100000000000000^53 ≤ 44259567893327^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346781831 10000000000 44259567893327 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247347739/10000000000 : ℝ)^69 ≤ (43191012386611/100000000000000 : ℝ)^53 := by
    have hnat : (5247347739 : ℕ)^69*100000000000000^53 ≤ 43191012386611^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247347739 10000000000 43191012386611 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (253833223/1250000000 : ℝ)^69 ≤ (1254941969957/10000000000000 : ℝ)^53 := by
    have hnat : (253833223 : ℕ)^69*10000000000000^53 ≤ 1254941969957^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253833223 1250000000 1254941969957 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346781831/10000000000 : ℝ), (5247347739/10000000000 : ℝ), (-253833223/1250000000 : ℝ)] ![(44259567893327/100000000000000 : ℝ), (43191012386611/100000000000000 : ℝ), (1254941969957/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346781831/10000000000 : ℝ)|^69 ≤ (44259567893327/100000000000000 : ℝ)^53
        have hw : |(5346781831/10000000000 : ℝ)|=(5346781831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247347739/10000000000 : ℝ)|^69 ≤ (43191012386611/100000000000000 : ℝ)^53
        have hw : |(5247347739/10000000000 : ℝ)|=(5247347739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-253833223/1250000000 : ℝ)|^69 ≤ (1254941969957/10000000000000 : ℝ)^53
        have hw : |(-253833223/1250000000 : ℝ)|=(253833223/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s5_3 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4297658239/10000000000 : ℝ)*x 0 + (2063218367/5000000000 : ℝ)*x 1 + (4475169393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4297658239/10000000000 : ℝ)^69 ≤ (33304998916143/100000000000000 : ℝ)^53 := by
    have hnat : (4297658239 : ℕ)^69*100000000000000^53 ≤ 33304998916143^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297658239 10000000000 33304998916143 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2063218367/5000000000 : ℝ)^69 ≤ (3948502628103/12500000000000 : ℝ)^53 := by
    have hnat : (2063218367 : ℕ)^69*12500000000000^53 ≤ 3948502628103^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063218367 5000000000 3948502628103 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4475169393/10000000000 : ℝ)^69 ≤ (7021396008199/20000000000000 : ℝ)^53 := by
    have hnat : (4475169393 : ℕ)^69*20000000000000^53 ≤ 7021396008199^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4475169393 10000000000 7021396008199 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4297658239/10000000000 : ℝ), (2063218367/5000000000 : ℝ), (4475169393/10000000000 : ℝ)] ![(33304998916143/100000000000000 : ℝ), (3948502628103/12500000000000 : ℝ), (7021396008199/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4297658239/10000000000 : ℝ)|^69 ≤ (33304998916143/100000000000000 : ℝ)^53
        have hw : |(4297658239/10000000000 : ℝ)|=(4297658239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2063218367/5000000000 : ℝ)|^69 ≤ (3948502628103/12500000000000 : ℝ)^53
        have hw : |(2063218367/5000000000 : ℝ)|=(2063218367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4475169393/10000000000 : ℝ)|^69 ≤ (7021396008199/20000000000000 : ℝ)^53
        have hw : |(4475169393/10000000000 : ℝ)|=(4475169393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s5_4 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1949426969/10000000000 : ℝ)*x 0 + (5247925837/10000000000 : ℝ)*x 1 + (540638769/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1949426969/10000000000 : ℝ)^69 ≤ (2974947263311/25000000000000 : ℝ)^53 := by
    have hnat : (1949426969 : ℕ)^69*25000000000000^53 ≤ 2974947263311^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1949426969 10000000000 2974947263311 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247925837/10000000000 : ℝ)^69 ≤ (8639441460597/20000000000000 : ℝ)^53 := by
    have hnat : (5247925837 : ℕ)^69*20000000000000^53 ≤ 8639441460597^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247925837 10000000000 8639441460597 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540638769/1000000000 : ℝ)^69 ≤ (11225750906067/25000000000000 : ℝ)^53 := by
    have hnat : (540638769 : ℕ)^69*25000000000000^53 ≤ 11225750906067^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540638769 1000000000 11225750906067 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1949426969/10000000000 : ℝ), (5247925837/10000000000 : ℝ), (540638769/1000000000 : ℝ)] ![(2974947263311/25000000000000 : ℝ), (8639441460597/20000000000000 : ℝ), (11225750906067/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1949426969/10000000000 : ℝ)|^69 ≤ (2974947263311/25000000000000 : ℝ)^53
        have hw : |(-1949426969/10000000000 : ℝ)|=(1949426969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247925837/10000000000 : ℝ)|^69 ≤ (8639441460597/20000000000000 : ℝ)^53
        have hw : |(5247925837/10000000000 : ℝ)|=(5247925837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540638769/1000000000 : ℝ)|^69 ≤ (11225750906067/25000000000000 : ℝ)^53
        have hw : |(540638769/1000000000 : ℝ)|=(540638769/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s5_5 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5305177479/10000000000 : ℝ)*x 0 + (-935812921/5000000000 : ℝ)*x 1 + (675798469/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305177479/10000000000 : ℝ)^69 ≤ (21905867817191/50000000000000 : ℝ)^53 := by
    have hnat : (5305177479 : ℕ)^69*50000000000000^53 ≤ 21905867817191^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305177479 10000000000 21905867817191 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (935812921/5000000000 : ℝ)^69 ≤ (11285260052789/100000000000000 : ℝ)^53 := by
    have hnat : (935812921 : ℕ)^69*100000000000000^53 ≤ 11285260052789^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935812921 5000000000 11285260052789 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675798469/1250000000 : ℝ)^69 ≤ (44903004294667/100000000000000 : ℝ)^53 := by
    have hnat : (675798469 : ℕ)^69*100000000000000^53 ≤ 44903004294667^53*1250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675798469 1250000000 44903004294667 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305177479/10000000000 : ℝ), (-935812921/5000000000 : ℝ), (675798469/1250000000 : ℝ)] ![(21905867817191/50000000000000 : ℝ), (11285260052789/100000000000000 : ℝ), (44903004294667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305177479/10000000000 : ℝ)|^69 ≤ (21905867817191/50000000000000 : ℝ)^53
        have hw : |(5305177479/10000000000 : ℝ)|=(5305177479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-935812921/5000000000 : ℝ)|^69 ≤ (11285260052789/100000000000000 : ℝ)^53
        have hw : |(-935812921/5000000000 : ℝ)|=(935812921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675798469/1250000000 : ℝ)|^69 ≤ (44903004294667/100000000000000 : ℝ)^53
        have hw : |(675798469/1250000000 : ℝ)|=(675798469/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s5_6 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (132629437/250000000 : ℝ)*x 0 + (5406387769/10000000000 : ℝ)*x 1 + (-935812909/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132629437/250000000 : ℝ)^69 ≤ (21905867822567/50000000000000 : ℝ)^53 := by
    have hnat : (132629437 : ℕ)^69*50000000000000^53 ≤ 21905867822567^53*250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132629437 250000000 21905867822567 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406387769/10000000000 : ℝ)^69 ≤ (22451502239243/50000000000000 : ℝ)^53 := by
    have hnat : (5406387769 : ℕ)^69*50000000000000^53 ≤ 22451502239243^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406387769 10000000000 22451502239243 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (935812909/5000000000 : ℝ)^69 ≤ (1128525986439/10000000000000 : ℝ)^53 := by
    have hnat : (935812909 : ℕ)^69*10000000000000^53 ≤ 1128525986439^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935812909 5000000000 1128525986439 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132629437/250000000 : ℝ), (5406387769/10000000000 : ℝ), (-935812909/5000000000 : ℝ)] ![(21905867822567/50000000000000 : ℝ), (22451502239243/50000000000000 : ℝ), (1128525986439/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132629437/250000000 : ℝ)|^69 ≤ (21905867822567/50000000000000 : ℝ)^53
        have hw : |(132629437/250000000 : ℝ)|=(132629437/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406387769/10000000000 : ℝ)|^69 ≤ (22451502239243/50000000000000 : ℝ)^53
        have hw : |(5406387769/10000000000 : ℝ)|=(5406387769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-935812909/5000000000 : ℝ)|^69 ≤ (1128525986439/10000000000000 : ℝ)^53
        have hw : |(-935812909/5000000000 : ℝ)|=(935812909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1456_s5_7 (p : ℝ) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2148841273/5000000000 : ℝ)*x 0 + (4473906429/10000000000 : ℝ)*x 1 + (4127706291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148841273/5000000000 : ℝ)^69 ≤ (3330524415117/10000000000000 : ℝ)^53 := by
    have hnat : (2148841273 : ℕ)^69*10000000000000^53 ≤ 3330524415117^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148841273 5000000000 3330524415117 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4473906429/10000000000 : ℝ)^69 ≤ (35094081823847/100000000000000 : ℝ)^53 := by
    have hnat : (4473906429 : ℕ)^69*100000000000000^53 ≤ 35094081823847^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4473906429 10000000000 35094081823847 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4127706291/10000000000 : ℝ)^69 ≤ (987521062649/3125000000000 : ℝ)^53 := by
    have hnat : (4127706291 : ℕ)^69*3125000000000^53 ≤ 987521062649^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127706291 10000000000 987521062649 3125000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2148841273/5000000000 : ℝ), (4473906429/10000000000 : ℝ), (4127706291/10000000000 : ℝ)] ![(3330524415117/10000000000000 : ℝ), (35094081823847/100000000000000 : ℝ), (987521062649/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2148841273/5000000000 : ℝ)|^69 ≤ (3330524415117/10000000000000 : ℝ)^53
        have hw : |(2148841273/5000000000 : ℝ)|=(2148841273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4473906429/10000000000 : ℝ)|^69 ≤ (35094081823847/100000000000000 : ℝ)^53
        have hw : |(4473906429/10000000000 : ℝ)|=(4473906429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4127706291/10000000000 : ℝ)|^69 ≤ (987521062649/3125000000000 : ℝ)^53
        have hw : |(4127706291/10000000000 : ℝ)|=(4127706291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1456_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15923767/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7397/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2843/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11391/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14773/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7397/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2843/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7397/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2843/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7397/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2843/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7397/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2843/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7397/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2843/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7397/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2843/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2843/25000 : ℝ) ^ (4415/1024 : ℝ) ≤ (2124019321273463/25000000000000000000 : ℝ) := by
    have hpowers : (2843/25000 : ℝ)^4415 ≤ (2124019321273463/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2843 : ℕ)^4415*25000000000000000000^1024 ≤ 2124019321273463^1024*25000^4415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2843 25000 2124019321273463 25000000000000000000 4415 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2843/25000 : ℝ)) (X := (2124019321273463/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7397/50000 : ℝ) ^ (4415/1024 : ℝ) ≤ (5282441192203603/20000000000000000000 : ℝ) := by
    have hpowers : (7397/50000 : ℝ)^4415 ≤ (5282441192203603/20000000000000000000 : ℝ)^1024 := by
      have hnat : (7397 : ℕ)^4415*20000000000000000000^1024 ≤ 5282441192203603^1024*50000^4415 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7397 50000 5282441192203603 20000000000000000000 4415 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7397/50000 : ℝ)) (X := (5282441192203603/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502124019321273463/12500000000000000000 : ℝ) ≤ (400015763380253/400000000000000 : ℝ) ^ (4415/1024 : ℝ) := by
    have hpowers : (12502124019321273463/12500000000000000000 : ℝ)^1024 ≤ (400015763380253/400000000000000 : ℝ)^4415 := by
      have hnat : (12502124019321273463 : ℕ)^1024*400000000000000^4415 ≤ 400015763380253^4415*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502124019321273463 12500000000000000000 400015763380253 400000000000000 1024 4415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400015763380253/400000000000000 : ℝ)) (X := (12502124019321273463/12500000000000000000 : ℝ)) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034908283246111867/100000000000000000000 : ℝ) ≤ (80006476338111/80000000000000 : ℝ) ^ (4415/1024 : ℝ) := by
    have hpowers : (100034908283246111867/100000000000000000000 : ℝ)^1024 ≤ (80006476338111/80000000000000 : ℝ)^4415 := by
      have hnat : (100034908283246111867 : ℕ)^1024*80000000000000^4415 ≤ 80006476338111^4415*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034908283246111867 100000000000000000000 80006476338111 80000000000000 1024 4415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (80006476338111/80000000000000 : ℝ)) (X := (100034908283246111867/100000000000000000000 : ℝ)) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005282441192203603/10000000000000000000 : ℝ) ≤ (400049000000857/400000000000000 : ℝ) ^ (4415/1024 : ℝ) := by
    have hpowers : (10005282441192203603/10000000000000000000 : ℝ)^1024 ≤ (400049000000857/400000000000000 : ℝ)^4415 := by
      have hnat : (10005282441192203603 : ℕ)^1024*400000000000000^4415 ≤ 400049000000857^4415*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005282441192203603 10000000000000000000 400049000000857 400000000000000 1024 4415 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400049000000857/400000000000000 : ℝ)) (X := (10005282441192203603/10000000000000000000 : ℝ)) (by norm_num) 4415 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2124019321273463/25000000000000000000 : ℝ) ≤ ((684237987718858539/684400000000000000 : ℝ)+2*(8309155151/6844000000000 : ℝ)*(2843/25000 : ℝ))^(4415/1024 : ℝ) := by
    rw [show (684237987718858539/684400000000000000 : ℝ)+2*(8309155151/6844000000000 : ℝ)*(2843/25000 : ℝ)=(400015763380253/400000000000000 : ℝ) by norm_num, show 1+2*(2124019321273463/25000000000000000000 : ℝ)=(12502124019321273463/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5282441192203603/20000000000000000000 : ℝ)+(2124019321273463/25000000000000000000 : ℝ) ≤ ((684237987718858539/684400000000000000 : ℝ)+(8309155151/6844000000000 : ℝ)*((7397/50000 : ℝ)+(2843/25000 : ℝ)))^(4415/1024 : ℝ) := by
    rw [show (684237987718858539/684400000000000000 : ℝ)+(8309155151/6844000000000 : ℝ)*((7397/50000 : ℝ)+(2843/25000 : ℝ))=(80006476338111/80000000000000 : ℝ) by norm_num, show 1+(5282441192203603/20000000000000000000 : ℝ)+(2124019321273463/25000000000000000000 : ℝ)=(100034908283246111867/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5282441192203603/20000000000000000000 : ℝ) ≤ ((684237987718858539/684400000000000000 : ℝ)+2*(8309155151/6844000000000 : ℝ)*(7397/50000 : ℝ))^(4415/1024 : ℝ) := by
    rw [show (684237987718858539/684400000000000000 : ℝ)+2*(8309155151/6844000000000 : ℝ)*(7397/50000 : ℝ)=(400049000000857/400000000000000 : ℝ) by norm_num, show 1+2*(5282441192203603/20000000000000000000 : ℝ)=(10005282441192203603/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (684237987718858539/684400000000000000 : ℝ)*(X 1 0+X 2 0)+(8309155151/6844000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4415/1024 : ℝ)) (lo := (2843/25000 : ℝ)) (hi := (7397/50000 : ℝ)) (c := (684237987718858539/684400000000000000 : ℝ)) (alpha := (8309155151/6844000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (684237987718858539/684400000000000000 : ℝ)*(X 0 1+X 2 1)+(8309155151/6844000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4415/1024 : ℝ)) (lo := (2843/25000 : ℝ)) (hi := (7397/50000 : ℝ)) (c := (684237987718858539/684400000000000000 : ℝ)) (alpha := (8309155151/6844000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (684237987718858539/684400000000000000 : ℝ)*(X 0 2+X 1 2)+(8309155151/6844000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4415/1024 : ℝ)) (lo := (2843/25000 : ℝ)) (hi := (7397/50000 : ℝ)) (c := (684237987718858539/684400000000000000 : ℝ)) (alpha := (8309155151/6844000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-487353953/2500000000 : ℝ)*X 0 0+(5406968801/10000000000 : ℝ)*X 0 1+(5247347739/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346781831/10000000000 : ℝ)*X 1 0+(-253833223/1250000000 : ℝ)*X 1 1+(5247347739/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346781831/10000000000 : ℝ)*X 2 0+(5247347739/10000000000 : ℝ)*X 2 1+(-253833223/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4297658239/10000000000 : ℝ)*X 0 0+(2063218367/5000000000 : ℝ)*X 0 1+(4475169393/10000000000 : ℝ)*X 0 2+(4297658239/10000000000 : ℝ)*X 1 0+(2063218367/5000000000 : ℝ)*X 1 1+(4475169393/10000000000 : ℝ)*X 1 2+(4297658239/10000000000 : ℝ)*X 2 0+(2063218367/5000000000 : ℝ)*X 2 1+(4475169393/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1949426969/10000000000 : ℝ)*X 0 0+(5247925837/10000000000 : ℝ)*X 0 1+(540638769/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305177479/10000000000 : ℝ)*X 1 0+(-935812921/5000000000 : ℝ)*X 1 1+(675798469/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132629437/250000000 : ℝ)*X 2 0+(5406387769/10000000000 : ℝ)*X 2 1+(-935812909/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2148841273/5000000000 : ℝ)*X 0 0+(4473906429/10000000000 : ℝ)*X 0 1+(4127706291/10000000000 : ℝ)*X 0 2+(2148841273/5000000000 : ℝ)*X 1 0+(4473906429/10000000000 : ℝ)*X 1 1+(4127706291/10000000000 : ℝ)*X 1 2+(2148841273/5000000000 : ℝ)*X 2 0+(4473906429/10000000000 : ℝ)*X 2 1+(4127706291/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1456_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11282458779166912072104249/1069375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1902994421/100000000000000 : ℝ)*(base19) + (27725809/1562500000000 : ℝ)*(base23) + (68728947/100000000000000 : ℝ)*(lower2) + (65578709/25000000000000 : ℝ)*(upper3) + (169153899/100000000000000 : ℝ)*(upper5) + (142695066137047/3125000000000 : ℝ)*(major0) + (142695066137047/3125000000000 : ℝ)*(major1) + (142695066137047/3125000000000 : ℝ)*(major2) + (125297589922433/2000000000000 : ℝ)*(sp0) + (783114745925007/12500000000000 : ℝ)*(sp1) + (6264918095942701/100000000000000 : ℝ)*(sp2) + (1433772009499367/50000000000000 : ℝ)*(sp3) + (40374272827/100000000000000 : ℝ)*(sp4) + (9995846951/50000000000000 : ℝ)*(sp7) + (716891002673159/25000000000000 : ℝ)*(f.failure) + (6264919870394477/100000000000000 : ℝ)*(f.sum) + (907473111657/342200000000000000000000000 : ℝ)*base66 + (94916579983727/73750000000000000000000000000 : ℝ)*base67 + (790708182890023/73750000000000000000000000000 : ℝ)*base70 + (589121016772477/73750000000000000000000000000 : ℝ)*base71 + (560269790361/171100000000000000000000000 : ℝ)*base73 + (1201445857685023/73750000000000000000000000000 : ℝ)*base76 + (59486854108773/73750000000000000000000000000 : ℝ)*base78 + (363434521528773/73750000000000000000000000000 : ℝ)*base80 + (16246051667/5346875000000000000000000 : ℝ)*base82 + (1069953/250000000000000000000 : ℝ)*base89 + (1069953/250000000000000000000 : ℝ)*base91 + (1069953/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6568294051302641792517/1711000000000000000000000000 : ℝ) := by norm_num
    linear_combination (126297319/25000000000000 : ℝ)*(base19) + (530545473/100000000000000 : ℝ)*(base23) + (87245739/100000000000000 : ℝ)*(upper3) + (2693717/50000000000000 : ℝ)*(lower4) + (34717001/50000000000000 : ℝ)*(upper5) + (4599584671142117/100000000000000 : ℝ)*(major0) + (4599584671142117/100000000000000 : ℝ)*(major1) + (4599584671142117/100000000000000 : ℝ)*(major2) + (462637681/4000000000000 : ℝ)*(sp1) + (333815833/2500000000000 : ℝ)*(sp2) + (394416646399599/6250000000000 : ℝ)*(sp4) + (6310654271262283/100000000000000 : ℝ)*(sp5) + (6310652459214791/100000000000000 : ℝ)*(sp6) + (722125717982139/25000000000000 : ℝ)*(sp7) + (722125717982139/25000000000000 : ℝ)*(f.failure) + (394416646399599/6250000000000 : ℝ)*(f.sum) + (2159198286771/342200000000000000000000000 : ℝ)*base65 + (10350986703193347/2360000000000000000000000000000 : ℝ)*base67 + (7931490102553347/2360000000000000000000000000000 : ℝ)*base69 + (1180302696166653/2360000000000000000000000000000 : ℝ)*base72 + (904392525717/1711000000000000000000000000 : ℝ)*base73 + (10274950441393347/2360000000000000000000000000000 : ℝ)*base75 + (2913116808646653/2360000000000000000000000000000 : ℝ)*base78 + (15391244181166653/2360000000000000000000000000000 : ℝ)*base80 + (495203043077/1711000000000000000000000000 : ℝ)*base81 + (902387/250000000000000000000 : ℝ)*base90 + (902387/250000000000000000000 : ℝ)*base92 + (902387/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1456_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15923767/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7397/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2843/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11391/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1456_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1456_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15923767/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (393/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10507/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11391/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1456_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1456_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1456_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4415/1024 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15923767/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (393/2500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10507/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11391/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14773/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1456_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
