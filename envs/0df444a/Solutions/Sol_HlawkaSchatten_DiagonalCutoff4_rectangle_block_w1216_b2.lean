-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1216_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:09:00.69456+00:00
-- url     : https://prove2.me/submissions/52b48ab3-33be-4297-be17-6657309f6acc

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
theorem support_rectangle_w1216_s6_0 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2131974441/10000000000 : ℝ)*x 0 + (2695952619/5000000000 : ℝ)*x 1 + (1053328881/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2131974441/10000000000 : ℝ)^8409 ≤ (2592419787067/20000000000000 : ℝ)^6361 := by
    have hnat : (2131974441 : ℕ)^8409*20000000000000^6361 ≤ 2592419787067^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131974441 10000000000 2592419787067 20000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695952619/5000000000 : ℝ)^8409 ≤ (44195032887571/100000000000000 : ℝ)^6361 := by
    have hnat : (2695952619 : ℕ)^8409*100000000000000^6361 ≤ 44195032887571^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695952619 5000000000 44195032887571 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053328881/2000000000 : ℝ)^8409 ≤ (4284286816169/10000000000000 : ℝ)^6361 := by
    have hnat : (1053328881 : ℕ)^8409*10000000000000^6361 ≤ 4284286816169^6361*2000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053328881 2000000000 4284286816169 10000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2131974441/10000000000 : ℝ), (2695952619/5000000000 : ℝ), (1053328881/2000000000 : ℝ)] ![(2592419787067/20000000000000 : ℝ), (44195032887571/100000000000000 : ℝ), (4284286816169/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2131974441/10000000000 : ℝ)|^8409 ≤ (2592419787067/20000000000000 : ℝ)^6361
        have hw : |(-2131974441/10000000000 : ℝ)|=(2131974441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695952619/5000000000 : ℝ)|^8409 ≤ (44195032887571/100000000000000 : ℝ)^6361
        have hw : |(2695952619/5000000000 : ℝ)|=(2695952619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053328881/2000000000 : ℝ)|^8409 ≤ (4284286816169/10000000000000 : ℝ)^6361
        have hw : |(1053328881/2000000000 : ℝ)|=(1053328881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s6_1 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672248667/5000000000 : ℝ)*x 0 + (-2195494053/10000000000 : ℝ)*x 1 + (1316661107/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672248667/5000000000 : ℝ)^8409 ≤ (43682071644697/100000000000000 : ℝ)^6361 := by
    have hnat : (2672248667 : ℕ)^8409*100000000000000^6361 ≤ 43682071644697^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672248667 5000000000 43682071644697 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2195494053/10000000000 : ℝ)^8409 ≤ (53900239719/400000000000 : ℝ)^6361 := by
    have hnat : (2195494053 : ℕ)^8409*400000000000^6361 ≤ 53900239719^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195494053 10000000000 53900239719 400000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316661107/2500000000 : ℝ)^8409 ≤ (10710717102257/25000000000000 : ℝ)^6361 := by
    have hnat : (1316661107 : ℕ)^8409*25000000000000^6361 ≤ 10710717102257^6361*2500000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316661107 2500000000 10710717102257 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672248667/5000000000 : ℝ), (-2195494053/10000000000 : ℝ), (1316661107/2500000000 : ℝ)] ![(43682071644697/100000000000000 : ℝ), (53900239719/400000000000 : ℝ), (10710717102257/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672248667/5000000000 : ℝ)|^8409 ≤ (43682071644697/100000000000000 : ℝ)^6361
        have hw : |(2672248667/5000000000 : ℝ)|=(2672248667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2195494053/10000000000 : ℝ)|^8409 ≤ (53900239719/400000000000 : ℝ)^6361
        have hw : |(-2195494053/10000000000 : ℝ)|=(2195494053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316661107/2500000000 : ℝ)|^8409 ≤ (10710717102257/25000000000000 : ℝ)^6361
        have hw : |(1316661107/2500000000 : ℝ)|=(1316661107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s6_2 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344497353/10000000000 : ℝ)*x 0 + (5266644423/10000000000 : ℝ)*x 1 + (-1097747017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344497353/10000000000 : ℝ)^8409 ≤ (43682071849987/100000000000000 : ℝ)^6361 := by
    have hnat : (5344497353 : ℕ)^8409*100000000000000^6361 ≤ 43682071849987^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344497353 10000000000 43682071849987 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266644423/10000000000 : ℝ)^8409 ≤ (42842868355259/100000000000000 : ℝ)^6361 := by
    have hnat : (5266644423 : ℕ)^8409*100000000000000^6361 ≤ 42842868355259^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266644423 10000000000 42842868355259 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097747017/5000000000 : ℝ)^8409 ≤ (1347505977559/10000000000000 : ℝ)^6361 := by
    have hnat : (1097747017 : ℕ)^8409*10000000000000^6361 ≤ 1347505977559^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097747017 5000000000 1347505977559 10000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344497353/10000000000 : ℝ), (5266644423/10000000000 : ℝ), (-1097747017/5000000000 : ℝ)] ![(43682071849987/100000000000000 : ℝ), (42842868355259/100000000000000 : ℝ), (1347505977559/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344497353/10000000000 : ℝ)|^8409 ≤ (43682071849987/100000000000000 : ℝ)^6361
        have hw : |(5344497353/10000000000 : ℝ)|=(5344497353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266644423/10000000000 : ℝ)|^8409 ≤ (42842868355259/100000000000000 : ℝ)^6361
        have hw : |(5266644423/10000000000 : ℝ)|=(5266644423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1097747017/5000000000 : ℝ)|^8409 ≤ (1347505977559/10000000000000 : ℝ)^6361
        have hw : |(-1097747017/5000000000 : ℝ)|=(1097747017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s6_3 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2177170161/5000000000 : ℝ)*x 0 + (528715297/1250000000 : ℝ)*x 1 + (1120636927/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177170161/5000000000 : ℝ)^8409 ≤ (16658623518389/50000000000000 : ℝ)^6361 := by
    have hnat : (2177170161 : ℕ)^8409*50000000000000^6361 ≤ 16658623518389^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177170161 5000000000 16658623518389 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528715297/1250000000 : ℝ)^8409 ≤ (32062582451657/100000000000000 : ℝ)^6361 := by
    have hnat : (528715297 : ℕ)^8409*100000000000000^6361 ≤ 32062582451657^6361*1250000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528715297 1250000000 32062582451657 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1120636927/2500000000 : ℝ)^8409 ≤ (17310085249369/50000000000000 : ℝ)^6361 := by
    have hnat : (1120636927 : ℕ)^8409*50000000000000^6361 ≤ 17310085249369^6361*2500000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120636927 2500000000 17310085249369 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177170161/5000000000 : ℝ), (528715297/1250000000 : ℝ), (1120636927/2500000000 : ℝ)] ![(16658623518389/50000000000000 : ℝ), (32062582451657/100000000000000 : ℝ), (17310085249369/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177170161/5000000000 : ℝ)|^8409 ≤ (16658623518389/50000000000000 : ℝ)^6361
        have hw : |(2177170161/5000000000 : ℝ)|=(2177170161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(528715297/1250000000 : ℝ)|^8409 ≤ (32062582451657/100000000000000 : ℝ)^6361
        have hw : |(528715297/1250000000 : ℝ)|=(528715297/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1120636927/2500000000 : ℝ)|^8409 ≤ (17310085249369/50000000000000 : ℝ)^6361
        have hw : |(1120636927/2500000000 : ℝ)|=(1120636927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s6_4 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2131979207/10000000000 : ℝ)*x 0 + (2633480553/5000000000 : ℝ)*x 1 + (5391587383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2131979207/10000000000 : ℝ)^8409 ≤ (12962137241307/100000000000000 : ℝ)^6361 := by
    have hnat : (2131979207 : ℕ)^8409*100000000000000^6361 ≤ 12962137241307^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131979207 10000000000 12962137241307 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633480553/5000000000 : ℝ)^8409 ≤ (4284627394597/10000000000000 : ℝ)^6361 := by
    have hnat : (2633480553 : ℕ)^8409*10000000000000^6361 ≤ 4284627394597^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633480553 5000000000 4284627394597 10000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391587383/10000000000 : ℝ)^8409 ≤ (44191588792801/100000000000000 : ℝ)^6361 := by
    have hnat : (5391587383 : ℕ)^8409*100000000000000^6361 ≤ 44191588792801^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391587383 10000000000 44191588792801 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2131979207/10000000000 : ℝ), (2633480553/5000000000 : ℝ), (5391587383/10000000000 : ℝ)] ![(12962137241307/100000000000000 : ℝ), (4284627394597/10000000000000 : ℝ), (44191588792801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2131979207/10000000000 : ℝ)|^8409 ≤ (12962137241307/100000000000000 : ℝ)^6361
        have hw : |(-2131979207/10000000000 : ℝ)|=(2131979207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633480553/5000000000 : ℝ)|^8409 ≤ (4284627394597/10000000000000 : ℝ)^6361
        have hw : |(2633480553/5000000000 : ℝ)|=(2633480553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391587383/10000000000 : ℝ)|^8409 ≤ (44191588792801/100000000000000 : ℝ)^6361
        have hw : |(5391587383/10000000000 : ℝ)|=(5391587383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s6_5 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664074161/1250000000 : ℝ)*x 0 + (-517637761/2500000000 : ℝ)*x 1 + (673948429/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664074161/1250000000 : ℝ)^8409 ≤ (43337687642647/100000000000000 : ℝ)^6361 := by
    have hnat : (664074161 : ℕ)^8409*100000000000000^6361 ≤ 43337687642647^6361*1250000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664074161 1250000000 43337687642647 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517637761/2500000000 : ℝ)^8409 ≤ (12470723021801/100000000000000 : ℝ)^6361 := by
    have hnat : (517637761 : ℕ)^8409*100000000000000^6361 ≤ 12470723021801^6361*2500000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517637761 2500000000 12470723021801 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673948429/1250000000 : ℝ)^8409 ≤ (11047897330933/25000000000000 : ℝ)^6361 := by
    have hnat : (673948429 : ℕ)^8409*25000000000000^6361 ≤ 11047897330933^6361*1250000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673948429 1250000000 11047897330933 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664074161/1250000000 : ℝ), (-517637761/2500000000 : ℝ), (673948429/1250000000 : ℝ)] ![(43337687642647/100000000000000 : ℝ), (12470723021801/100000000000000 : ℝ), (11047897330933/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664074161/1250000000 : ℝ)|^8409 ≤ (43337687642647/100000000000000 : ℝ)^6361
        have hw : |(664074161/1250000000 : ℝ)|=(664074161/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-517637761/2500000000 : ℝ)|^8409 ≤ (12470723021801/100000000000000 : ℝ)^6361
        have hw : |(-517637761/2500000000 : ℝ)|=(517637761/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673948429/1250000000 : ℝ)|^8409 ≤ (11047897330933/25000000000000 : ℝ)^6361
        have hw : |(673948429/1250000000 : ℝ)|=(673948429/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s6_6 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (531259323/1000000000 : ℝ)*x 0 + (336974217/625000000 : ℝ)*x 1 + (-517637767/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531259323/1000000000 : ℝ)^8409 ≤ (43337687017177/100000000000000 : ℝ)^6361 := by
    have hnat : (531259323 : ℕ)^8409*100000000000000^6361 ≤ 43337687017177^6361*1000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531259323 1000000000 43337687017177 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336974217/625000000 : ℝ)^8409 ≤ (8838317951429/20000000000000 : ℝ)^6361 := by
    have hnat : (336974217 : ℕ)^8409*20000000000000^6361 ≤ 8838317951429^6361*625000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336974217 625000000 8838317951429 20000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517637767/2500000000 : ℝ)^8409 ≤ (1247072321289/10000000000000 : ℝ)^6361 := by
    have hnat : (517637767 : ℕ)^8409*10000000000000^6361 ≤ 1247072321289^6361*2500000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517637767 2500000000 1247072321289 10000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531259323/1000000000 : ℝ), (336974217/625000000 : ℝ), (-517637767/2500000000 : ℝ)] ![(43337687017177/100000000000000 : ℝ), (8838317951429/20000000000000 : ℝ), (1247072321289/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531259323/1000000000 : ℝ)|^8409 ≤ (43337687017177/100000000000000 : ℝ)^6361
        have hw : |(531259323/1000000000 : ℝ)|=(531259323/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(336974217/625000000 : ℝ)|^8409 ≤ (8838317951429/20000000000000 : ℝ)^6361
        have hw : |(336974217/625000000 : ℝ)|=(336974217/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-517637767/2500000000 : ℝ)|^8409 ≤ (1247072321289/10000000000000 : ℝ)^6361
        have hw : |(-517637767/2500000000 : ℝ)|=(517637767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s6_7 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2177174971/5000000000 : ℝ)*x 0 + (4481908541/10000000000 : ℝ)*x 1 + (4230363861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177174971/5000000000 : ℝ)^8409 ≤ (3331734434307/10000000000000 : ℝ)^6361 := by
    have hnat : (2177174971 : ℕ)^8409*10000000000000^6361 ≤ 3331734434307^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177174971 5000000000 3331734434307 10000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4481908541/10000000000 : ℝ)^8409 ≤ (6922728958217/20000000000000 : ℝ)^6361 := by
    have hnat : (4481908541 : ℕ)^8409*20000000000000^6361 ≤ 6922728958217^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481908541 10000000000 6922728958217 20000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4230363861/10000000000 : ℝ)^8409 ≤ (32069010848833/100000000000000 : ℝ)^6361 := by
    have hnat : (4230363861 : ℕ)^8409*100000000000000^6361 ≤ 32069010848833^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230363861 10000000000 32069010848833 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177174971/5000000000 : ℝ), (4481908541/10000000000 : ℝ), (4230363861/10000000000 : ℝ)] ![(3331734434307/10000000000000 : ℝ), (6922728958217/20000000000000 : ℝ), (32069010848833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177174971/5000000000 : ℝ)|^8409 ≤ (3331734434307/10000000000000 : ℝ)^6361
        have hw : |(2177174971/5000000000 : ℝ)|=(2177174971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4481908541/10000000000 : ℝ)|^8409 ≤ (6922728958217/20000000000000 : ℝ)^6361
        have hw : |(4481908541/10000000000 : ℝ)|=(4481908541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4230363861/10000000000 : ℝ)|^8409 ≤ (32069010848833/100000000000000 : ℝ)^6361
        have hw : |(4230363861/10000000000 : ℝ)|=(4230363861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1216_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11419/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5721/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (881/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14119/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11419/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14119/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11419/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14119/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11419/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14119/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11419/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14119/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11419/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14119/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11419/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11419/100000 : ℝ) ^ (1051/256 : ℝ) ≤ (13524508856867521/100000000000000000000 : ℝ) := by
    have hpowers : (11419/100000 : ℝ)^1051 ≤ (13524508856867521/100000000000000000000 : ℝ)^256 := by
      have hnat : (11419 : ℕ)^1051*100000000000000000000^256 ≤ 13524508856867521^256*100000^1051 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11419 100000 13524508856867521 100000000000000000000 1051 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11419/100000 : ℝ)) (X := (13524508856867521/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14119/100000 : ℝ) ^ (1051/256 : ℝ) ≤ (4040700394397773/12500000000000000000 : ℝ) := by
    have hpowers : (14119/100000 : ℝ)^1051 ≤ (4040700394397773/12500000000000000000 : ℝ)^256 := by
      have hnat : (14119 : ℕ)^1051*12500000000000000000^256 ≤ 4040700394397773^256*100000^1051 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14119 100000 4040700394397773 12500000000000000000 1051 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14119/100000 : ℝ)) (X := (4040700394397773/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013524508856867521/50000000000000000000 : ℝ) ≤ (5000329392970923/5000000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (50013524508856867521/50000000000000000000 : ℝ)^256 ≤ (5000329392970923/5000000000000000 : ℝ)^1051 := by
      have hnat : (50013524508856867521 : ℕ)^256*5000000000000000^1051 ≤ 5000329392970923^1051*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013524508856867521 50000000000000000000 5000329392970923 5000000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000329392970923/5000000000000000 : ℝ)) (X := (50013524508856867521/50000000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (20009170022402409941/20000000000000000000 : ℝ) ≤ (10001116612159461/10000000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (20009170022402409941/20000000000000000000 : ℝ)^256 ≤ (10001116612159461/10000000000000000 : ℝ)^1051 := by
      have hnat : (20009170022402409941 : ℕ)^256*10000000000000000^1051 ≤ 10001116612159461^1051*20000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20009170022402409941 20000000000000000000 10001116612159461 10000000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001116612159461/10000000000000000 : ℝ)) (X := (20009170022402409941/20000000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254040700394397773/6250000000000000000 : ℝ) ≤ (2500393609594269/2500000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (6254040700394397773/6250000000000000000 : ℝ)^256 ≤ (2500393609594269/2500000000000000 : ℝ)^1051 := by
      have hnat : (6254040700394397773 : ℕ)^256*2500000000000000^1051 ≤ 2500393609594269^1051*6250000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254040700394397773 6250000000000000000 2500393609594269 2500000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500393609594269/2500000000000000 : ℝ)) (X := (6254040700394397773/6250000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13524508856867521/100000000000000000000 : ℝ) ≤ ((299903587632056587/300000000000000000 : ℝ)+2*(10173915947/6000000000000 : ℝ)*(11419/100000 : ℝ))^(1051/256 : ℝ) := by
    rw [show (299903587632056587/300000000000000000 : ℝ)+2*(10173915947/6000000000000 : ℝ)*(11419/100000 : ℝ)=(5000329392970923/5000000000000000 : ℝ) by norm_num, show 1+2*(13524508856867521/100000000000000000000 : ℝ)=(50013524508856867521/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4040700394397773/12500000000000000000 : ℝ)+(13524508856867521/100000000000000000000 : ℝ) ≤ ((299903587632056587/300000000000000000 : ℝ)+(10173915947/6000000000000 : ℝ)*((14119/100000 : ℝ)+(11419/100000 : ℝ)))^(1051/256 : ℝ) := by
    rw [show (299903587632056587/300000000000000000 : ℝ)+(10173915947/6000000000000 : ℝ)*((14119/100000 : ℝ)+(11419/100000 : ℝ))=(10001116612159461/10000000000000000 : ℝ) by norm_num, show 1+(4040700394397773/12500000000000000000 : ℝ)+(13524508856867521/100000000000000000000 : ℝ)=(20009170022402409941/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4040700394397773/12500000000000000000 : ℝ) ≤ ((299903587632056587/300000000000000000 : ℝ)+2*(10173915947/6000000000000 : ℝ)*(14119/100000 : ℝ))^(1051/256 : ℝ) := by
    rw [show (299903587632056587/300000000000000000 : ℝ)+2*(10173915947/6000000000000 : ℝ)*(14119/100000 : ℝ)=(2500393609594269/2500000000000000 : ℝ) by norm_num, show 1+2*(4040700394397773/12500000000000000000 : ℝ)=(6254040700394397773/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (299903587632056587/300000000000000000 : ℝ)*(X 1 0+X 2 0)+(10173915947/6000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (11419/100000 : ℝ)) (hi := (14119/100000 : ℝ)) (c := (299903587632056587/300000000000000000 : ℝ)) (alpha := (10173915947/6000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (299903587632056587/300000000000000000 : ℝ)*(X 0 1+X 2 1)+(10173915947/6000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (11419/100000 : ℝ)) (hi := (14119/100000 : ℝ)) (c := (299903587632056587/300000000000000000 : ℝ)) (alpha := (10173915947/6000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (299903587632056587/300000000000000000 : ℝ)*(X 0 2+X 1 2)+(10173915947/6000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (11419/100000 : ℝ)) (hi := (14119/100000 : ℝ)) (c := (299903587632056587/300000000000000000 : ℝ)) (alpha := (10173915947/6000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2131974441/10000000000 : ℝ)*X 0 0+(2695952619/5000000000 : ℝ)*X 0 1+(1053328881/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672248667/5000000000 : ℝ)*X 1 0+(-2195494053/10000000000 : ℝ)*X 1 1+(1316661107/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344497353/10000000000 : ℝ)*X 2 0+(5266644423/10000000000 : ℝ)*X 2 1+(-1097747017/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2177170161/5000000000 : ℝ)*X 0 0+(528715297/1250000000 : ℝ)*X 0 1+(1120636927/2500000000 : ℝ)*X 0 2+(2177170161/5000000000 : ℝ)*X 1 0+(528715297/1250000000 : ℝ)*X 1 1+(1120636927/2500000000 : ℝ)*X 1 2+(2177170161/5000000000 : ℝ)*X 2 0+(528715297/1250000000 : ℝ)*X 2 1+(1120636927/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2131979207/10000000000 : ℝ)*X 0 0+(2633480553/5000000000 : ℝ)*X 0 1+(5391587383/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664074161/1250000000 : ℝ)*X 1 0+(-517637761/2500000000 : ℝ)*X 1 1+(673948429/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((531259323/1000000000 : ℝ)*X 2 0+(336974217/625000000 : ℝ)*X 2 1+(-517637767/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2177174971/5000000000 : ℝ)*X 0 0+(4481908541/10000000000 : ℝ)*X 0 1+(4230363861/10000000000 : ℝ)*X 0 2+(2177174971/5000000000 : ℝ)*X 1 0+(4481908541/10000000000 : ℝ)*X 1 1+(4230363861/10000000000 : ℝ)*X 1 2+(2177174971/5000000000 : ℝ)*X 2 0+(4481908541/10000000000 : ℝ)*X 2 1+(4230363861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17636787175809425719251447/2500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (286257167/20000000000000 : ℝ)*(base19) + (678760493/50000000000000 : ℝ)*(base23) + (27296053/50000000000000 : ℝ)*(lower2) + (89249997/50000000000000 : ℝ)*(upper3) + (1087967/781250000000 : ℝ)*(upper5) + (2984691087288219/50000000000000 : ℝ)*(major0) + (2984691087288219/50000000000000 : ℝ)*(major1) + (2984691087288219/50000000000000 : ℝ)*(major2) + (399169133587051/5000000000000 : ℝ)*(sp0) + (159668452931449/2000000000000 : ℝ)*(sp1) + (7983422720337299/100000000000000 : ℝ)*(sp2) + (1977659569443691/50000000000000 : ℝ)*(sp3) + (8281223453/20000000000000 : ℝ)*(sp4) + (20897250037/100000000000000 : ℝ)*(sp7) + (197767001806871/5000000000000 : ℝ)*(f.failure) + (1596684815571657/20000000000000 : ℝ)*(f.sum) + (191664533019/50000000000000000000000000 : ℝ)*base66 + (26481825907032851/5000000000000000000000000000000 : ℝ)*base67 + (51395273862032851/5000000000000000000000000000000 : ℝ)*base69 + (23519322387967149/5000000000000000000000000000000 : ℝ)*base72 + (418905486181/50000000000000000000000000 : ℝ)*base73 + (63863533837032851/5000000000000000000000000000000 : ℝ)*base75 + (76068428622967149/5000000000000000000000000000000 : ℝ)*base78 + (31933447772032851/5000000000000000000000000000000 : ℝ)*base79 + (48201818781/50000000000000000000000000 : ℝ)*base81 + (436547/50000000000000000000 : ℝ)*base89 + (436547/50000000000000000000 : ℝ)*base91 + (436547/50000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1043510689686953553163089/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14662923/781250000000 : ℝ)*(base19) + (244449333/12500000000000 : ℝ)*(base23) + (240774371/100000000000000 : ℝ)*(upper3) + (39387681/50000000000000 : ℝ)*(lower4) + (218978883/100000000000000 : ℝ)*(upper5) + (239988445355547/4000000000000 : ℝ)*(major0) + (239988445355547/4000000000000 : ℝ)*(major1) + (239988445355547/4000000000000 : ℝ)*(major2) + (53102211441/100000000000000 : ℝ)*(sp1) + (56109650527/100000000000000 : ℝ)*(sp2) + (802398577611319/10000000000000 : ℝ)*(sp4) + (1604786159409521/20000000000000 : ℝ)*(sp5) + (2005981927717/25000000000 : ℝ)*(sp6) + (496929517978407/12500000000000 : ℝ)*(sp7) + (496929517978407/12500000000000 : ℝ)*(f.failure) + (802398577611319/10000000000000 : ℝ)*(f.sum) + (4789995857/800000000000000000000000 : ℝ)*base66 + (2964351841470637/400000000000000000000000000000 : ℝ)*base68 + (1640150061470637/400000000000000000000000000000 : ℝ)*base70 + (574836261470637/400000000000000000000000000000 : ℝ)*base72 + (44419198009/4000000000000000000000000 : ℝ)*base74 + (2464277796670637/400000000000000000000000000000 : ℝ)*base76 + (999604860270637/400000000000000000000000000000 : ℝ)*base78 + (2649380646129363/400000000000000000000000000000 : ℝ)*base79 + (24292125989/4000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1622499/125000000000000000000 : ℝ)*base89 + (1622499/125000000000000000000 : ℝ)*base91 + (1622499/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1216_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11419/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5721/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (881/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1216_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1216_s7_0 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2131990127/10000000000 : ℝ)*x 0 + (5391685823/10000000000 : ℝ)*x 1 + (5266853761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2131990127/10000000000 : ℝ)^8409 ≤ (6481112504593/50000000000000 : ℝ)^6361 := by
    have hnat : (2131990127 : ℕ)^8409*50000000000000^6361 ≤ 6481112504593^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131990127 10000000000 6481112504593 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391685823/10000000000 : ℝ)^8409 ≤ (8838531085057/20000000000000 : ℝ)^6361 := by
    have hnat : (5391685823 : ℕ)^8409*20000000000000^6361 ≤ 8838531085057^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391685823 10000000000 8838531085057 20000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266853761/10000000000 : ℝ)^8409 ≤ (42845119556647/100000000000000 : ℝ)^6361 := by
    have hnat : (5266853761 : ℕ)^8409*100000000000000^6361 ≤ 42845119556647^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266853761 10000000000 42845119556647 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2131990127/10000000000 : ℝ), (5391685823/10000000000 : ℝ), (5266853761/10000000000 : ℝ)] ![(6481112504593/50000000000000 : ℝ), (8838531085057/20000000000000 : ℝ), (42845119556647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2131990127/10000000000 : ℝ)|^8409 ≤ (6481112504593/50000000000000 : ℝ)^6361
        have hw : |(-2131990127/10000000000 : ℝ)|=(2131990127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391685823/10000000000 : ℝ)|^8409 ≤ (8838531085057/20000000000000 : ℝ)^6361
        have hw : |(5391685823/10000000000 : ℝ)|=(5391685823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266853761/10000000000 : ℝ)|^8409 ≤ (42845119556647/100000000000000 : ℝ)^6361
        have hw : |(5266853761/10000000000 : ℝ)|=(5266853761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s7_1 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344442739/10000000000 : ℝ)*x 0 + (-1097644651/5000000000 : ℝ)*x 1 + (5266853761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344442739/10000000000 : ℝ)^8409 ≤ (43681481759531/100000000000000 : ℝ)^6361 := by
    have hnat : (5344442739 : ℕ)^8409*100000000000000^6361 ≤ 43681481759531^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344442739 10000000000 43681481759531 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097644651/5000000000 : ℝ)^8409 ≤ (6736699336213/50000000000000 : ℝ)^6361 := by
    have hnat : (1097644651 : ℕ)^8409*50000000000000^6361 ≤ 6736699336213^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097644651 5000000000 6736699336213 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266853761/10000000000 : ℝ)^8409 ≤ (42845119556647/100000000000000 : ℝ)^6361 := by
    have hnat : (5266853761 : ℕ)^8409*100000000000000^6361 ≤ 42845119556647^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266853761 10000000000 42845119556647 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344442739/10000000000 : ℝ), (-1097644651/5000000000 : ℝ), (5266853761/10000000000 : ℝ)] ![(43681481759531/100000000000000 : ℝ), (6736699336213/50000000000000 : ℝ), (42845119556647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344442739/10000000000 : ℝ)|^8409 ≤ (43681481759531/100000000000000 : ℝ)^6361
        have hw : |(5344442739/10000000000 : ℝ)|=(5344442739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1097644651/5000000000 : ℝ)|^8409 ≤ (6736699336213/50000000000000 : ℝ)^6361
        have hw : |(-1097644651/5000000000 : ℝ)|=(1097644651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266853761/10000000000 : ℝ)|^8409 ≤ (42845119556647/100000000000000 : ℝ)^6361
        have hw : |(5266853761/10000000000 : ℝ)|=(5266853761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s7_2 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344442739/10000000000 : ℝ)*x 0 + (5266853759/10000000000 : ℝ)*x 1 + (-274411163/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344442739/10000000000 : ℝ)^8409 ≤ (43681481759531/100000000000000 : ℝ)^6361 := by
    have hnat : (5344442739 : ℕ)^8409*100000000000000^6361 ≤ 43681481759531^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344442739 10000000000 43681481759531 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266853759/10000000000 : ℝ)^8409 ≤ (42845119535139/100000000000000 : ℝ)^6361 := by
    have hnat : (5266853759 : ℕ)^8409*100000000000000^6361 ≤ 42845119535139^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266853759 10000000000 42845119535139 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274411163/1250000000 : ℝ)^8409 ≤ (13473398688653/100000000000000 : ℝ)^6361 := by
    have hnat : (274411163 : ℕ)^8409*100000000000000^6361 ≤ 13473398688653^6361*1250000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274411163 1250000000 13473398688653 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344442739/10000000000 : ℝ), (5266853759/10000000000 : ℝ), (-274411163/1250000000 : ℝ)] ![(43681481759531/100000000000000 : ℝ), (42845119535139/100000000000000 : ℝ), (13473398688653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344442739/10000000000 : ℝ)|^8409 ≤ (43681481759531/100000000000000 : ℝ)^6361
        have hw : |(5344442739/10000000000 : ℝ)|=(5344442739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266853759/10000000000 : ℝ)|^8409 ≤ (42845119535139/100000000000000 : ℝ)^6361
        have hw : |(5266853759/10000000000 : ℝ)|=(5266853759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-274411163/1250000000 : ℝ)|^8409 ≤ (13473398688653/100000000000000 : ℝ)^6361
        have hw : |(-274411163/1250000000 : ℝ)|=(274411163/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s7_3 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (217717557/500000000 : ℝ)*x 0 + (4230153687/10000000000 : ℝ)*x 1 + (2241056827/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217717557/500000000 : ℝ)^8409 ≤ (33317356460843/100000000000000 : ℝ)^6361 := by
    have hnat : (217717557 : ℕ)^8409*100000000000000^6361 ≤ 33317356460843^6361*500000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217717557 500000000 33317356460843 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4230153687/10000000000 : ℝ)^8409 ≤ (32066904635711/100000000000000 : ℝ)^6361 := by
    have hnat : (4230153687 : ℕ)^8409*100000000000000^6361 ≤ 32066904635711^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230153687 10000000000 32066904635711 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2241056827/5000000000 : ℝ)^8409 ≤ (1384629556081/4000000000000 : ℝ)^6361 := by
    have hnat : (2241056827 : ℕ)^8409*4000000000000^6361 ≤ 1384629556081^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241056827 5000000000 1384629556081 4000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(217717557/500000000 : ℝ), (4230153687/10000000000 : ℝ), (2241056827/5000000000 : ℝ)] ![(33317356460843/100000000000000 : ℝ), (32066904635711/100000000000000 : ℝ), (1384629556081/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(217717557/500000000 : ℝ)|^8409 ≤ (33317356460843/100000000000000 : ℝ)^6361
        have hw : |(217717557/500000000 : ℝ)|=(217717557/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4230153687/10000000000 : ℝ)|^8409 ≤ (32066904635711/100000000000000 : ℝ)^6361
        have hw : |(4230153687/10000000000 : ℝ)|=(4230153687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2241056827/5000000000 : ℝ)|^8409 ≤ (1384629556081/4000000000000 : ℝ)^6361
        have hw : |(2241056827/5000000000 : ℝ)|=(2241056827/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s7_4 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1065997421/5000000000 : ℝ)*x 0 + (5267168281/10000000000 : ℝ)*x 1 + (2695685081/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1065997421/5000000000 : ℝ)^8409 ≤ (25316919737/195312500000 : ℝ)^6361 := by
    have hnat : (1065997421 : ℕ)^8409*195312500000^6361 ≤ 25316919737^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1065997421 5000000000 25316919737 195312500000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267168281/10000000000 : ℝ)^8409 ≤ (1071212548241/2500000000000 : ℝ)^6361 := by
    have hnat : (5267168281 : ℕ)^8409*2500000000000^6361 ≤ 1071212548241^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267168281 10000000000 1071212548241 2500000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695685081/5000000000 : ℝ)^8409 ≤ (172614199797/390625000000 : ℝ)^6361 := by
    have hnat : (2695685081 : ℕ)^8409*390625000000^6361 ≤ 172614199797^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695685081 5000000000 172614199797 390625000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1065997421/5000000000 : ℝ), (5267168281/10000000000 : ℝ), (2695685081/5000000000 : ℝ)] ![(25316919737/195312500000 : ℝ), (1071212548241/2500000000000 : ℝ), (172614199797/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1065997421/5000000000 : ℝ)|^8409 ≤ (25316919737/195312500000 : ℝ)^6361
        have hw : |(-1065997421/5000000000 : ℝ)|=(1065997421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267168281/10000000000 : ℝ)|^8409 ≤ (1071212548241/2500000000000 : ℝ)^6361
        have hw : |(5267168281/10000000000 : ℝ)|=(5267168281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695685081/5000000000 : ℝ)|^8409 ≤ (172614199797/390625000000 : ℝ)^6361
        have hw : |(2695685081/5000000000 : ℝ)|=(2695685081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s7_5 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656323893/5000000000 : ℝ)*x 0 + (-1035386451/5000000000 : ℝ)*x 1 + (2695685081/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656323893/5000000000 : ℝ)^8409 ≤ (5417284418459/12500000000000 : ℝ)^6361 := by
    have hnat : (2656323893 : ℕ)^8409*12500000000000^6361 ≤ 5417284418459^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656323893 5000000000 5417284418459 12500000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035386451/5000000000 : ℝ)^8409 ≤ (1559061186967/12500000000000 : ℝ)^6361 := by
    have hnat : (1035386451 : ℕ)^8409*12500000000000^6361 ≤ 1559061186967^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035386451 5000000000 1559061186967 12500000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695685081/5000000000 : ℝ)^8409 ≤ (172614199797/390625000000 : ℝ)^6361 := by
    have hnat : (2695685081 : ℕ)^8409*390625000000^6361 ≤ 172614199797^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695685081 5000000000 172614199797 390625000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656323893/5000000000 : ℝ), (-1035386451/5000000000 : ℝ), (2695685081/5000000000 : ℝ)] ![(5417284418459/12500000000000 : ℝ), (1559061186967/12500000000000 : ℝ), (172614199797/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656323893/5000000000 : ℝ)|^8409 ≤ (5417284418459/12500000000000 : ℝ)^6361
        have hw : |(2656323893/5000000000 : ℝ)|=(2656323893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1035386451/5000000000 : ℝ)|^8409 ≤ (1559061186967/12500000000000 : ℝ)^6361
        have hw : |(-1035386451/5000000000 : ℝ)|=(1035386451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695685081/5000000000 : ℝ)|^8409 ≤ (172614199797/390625000000 : ℝ)^6361
        have hw : |(2695685081/5000000000 : ℝ)|=(2695685081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s7_6 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656323893/5000000000 : ℝ)*x 0 + (2695685081/5000000000 : ℝ)*x 1 + (-1035386451/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656323893/5000000000 : ℝ)^8409 ≤ (5417284418459/12500000000000 : ℝ)^6361 := by
    have hnat : (2656323893 : ℕ)^8409*12500000000000^6361 ≤ 5417284418459^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656323893 5000000000 5417284418459 12500000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695685081/5000000000 : ℝ)^8409 ≤ (172614199797/390625000000 : ℝ)^6361 := by
    have hnat : (2695685081 : ℕ)^8409*390625000000^6361 ≤ 172614199797^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695685081 5000000000 172614199797 390625000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035386451/5000000000 : ℝ)^8409 ≤ (1559061186967/12500000000000 : ℝ)^6361 := by
    have hnat : (1035386451 : ℕ)^8409*12500000000000^6361 ≤ 1559061186967^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035386451 5000000000 1559061186967 12500000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656323893/5000000000 : ℝ), (2695685081/5000000000 : ℝ), (-1035386451/5000000000 : ℝ)] ![(5417284418459/12500000000000 : ℝ), (172614199797/390625000000 : ℝ), (1559061186967/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656323893/5000000000 : ℝ)|^8409 ≤ (5417284418459/12500000000000 : ℝ)^6361
        have hw : |(2656323893/5000000000 : ℝ)|=(2656323893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695685081/5000000000 : ℝ)|^8409 ≤ (172614199797/390625000000 : ℝ)^6361
        have hw : |(2695685081/5000000000 : ℝ)|=(2695685081/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1035386451/5000000000 : ℝ)|^8409 ≤ (1559061186967/12500000000000 : ℝ)^6361
        have hw : |(-1035386451/5000000000 : ℝ)|=(1035386451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s7_7 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2177180327/5000000000 : ℝ)*x 0 + (179259153/400000000 : ℝ)*x 1 + (2115395409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177180327/5000000000 : ℝ)^8409 ≤ (16658726347511/50000000000000 : ℝ)^6361 := by
    have hnat : (2177180327 : ℕ)^8409*50000000000000^6361 ≤ 16658726347511^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177180327 5000000000 16658726347511 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179259153/400000000 : ℝ)^8409 ≤ (34609257685157/100000000000000 : ℝ)^6361 := by
    have hnat : (179259153 : ℕ)^8409*100000000000000^6361 ≤ 34609257685157^6361*400000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179259153 400000000 34609257685157 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2115395409/5000000000 : ℝ)^8409 ≤ (16036644804737/50000000000000 : ℝ)^6361 := by
    have hnat : (2115395409 : ℕ)^8409*50000000000000^6361 ≤ 16036644804737^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115395409 5000000000 16036644804737 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177180327/5000000000 : ℝ), (179259153/400000000 : ℝ), (2115395409/5000000000 : ℝ)] ![(16658726347511/50000000000000 : ℝ), (34609257685157/100000000000000 : ℝ), (16036644804737/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177180327/5000000000 : ℝ)|^8409 ≤ (16658726347511/50000000000000 : ℝ)^6361
        have hw : |(2177180327/5000000000 : ℝ)|=(2177180327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(179259153/400000000 : ℝ)|^8409 ≤ (34609257685157/100000000000000 : ℝ)^6361
        have hw : |(179259153/400000000 : ℝ)|=(179259153/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2115395409/5000000000 : ℝ)|^8409 ≤ (16036644804737/50000000000000 : ℝ)^6361
        have hw : |(2115395409/5000000000 : ℝ)|=(2115395409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1216_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (881/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5721/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11447/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14091/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (881/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5721/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (881/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5721/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (881/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5721/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (881/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5721/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (881/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5721/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (881/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5721/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5721/50000 : ℝ) ^ (1051/256 : ℝ) ≤ (109093565887949/800000000000000000 : ℝ) := by
    have hpowers : (5721/50000 : ℝ)^1051 ≤ (109093565887949/800000000000000000 : ℝ)^256 := by
      have hnat : (5721 : ℕ)^1051*800000000000000000^256 ≤ 109093565887949^256*50000^1051 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5721 50000 109093565887949 800000000000000000 1051 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5721/50000 : ℝ)) (X := (109093565887949/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hpowhi : (881/6250 : ℝ) ^ (1051/256 : ℝ) ≤ (16054980257858403/50000000000000000000 : ℝ) := by
    have hpowers : (881/6250 : ℝ)^1051 ≤ (16054980257858403/50000000000000000000 : ℝ)^256 := by
      have hnat : (881 : ℕ)^1051*50000000000000000000^256 ≤ 16054980257858403^256*6250^1051 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        881 6250 16054980257858403 50000000000000000000 1051 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (881/6250 : ℝ)) (X := (16054980257858403/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (400109093565887949/400000000000000000 : ℝ) ≤ (2000132850012037/2000000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (400109093565887949/400000000000000000 : ℝ)^256 ≤ (2000132850012037/2000000000000000 : ℝ)^1051 := by
      have hnat : (400109093565887949 : ℕ)^256*2000000000000000^1051 ≤ 2000132850012037^1051*400000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        400109093565887949 400000000000000000 2000132850012037 2000000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000132850012037/2000000000000000 : ℝ)) (X := (400109093565887949/400000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045746656251710431/100000000000000000000 : ℝ) ≤ (62506963081763/62500000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (100045746656251710431/100000000000000000000 : ℝ)^256 ≤ (62506963081763/62500000000000 : ℝ)^1051 := by
      have hnat : (100045746656251710431 : ℕ)^256*62500000000000^1051 ≤ 62506963081763^1051*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045746656251710431 100000000000000000000 62506963081763 62500000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62506963081763/62500000000000 : ℝ)) (X := (100045746656251710431/100000000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016054980257858403/25000000000000000000 : ℝ) ≤ (400062557444159/400000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (25016054980257858403/25000000000000000000 : ℝ)^256 ≤ (400062557444159/400000000000000 : ℝ)^1051 := by
      have hnat : (25016054980257858403 : ℕ)^256*400000000000000^1051 ≤ 400062557444159^1051*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016054980257858403 25000000000000000000 400062557444159 400000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400062557444159/400000000000000 : ℝ)) (X := (25016054980257858403/25000000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(109093565887949/800000000000000000 : ℝ) ≤ ((2653146871194668581/2654000000000000000 : ℝ)+2*(89968604379/53080000000000 : ℝ)*(5721/50000 : ℝ))^(1051/256 : ℝ) := by
    rw [show (2653146871194668581/2654000000000000000 : ℝ)+2*(89968604379/53080000000000 : ℝ)*(5721/50000 : ℝ)=(2000132850012037/2000000000000000 : ℝ) by norm_num, show 1+2*(109093565887949/800000000000000000 : ℝ)=(400109093565887949/400000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16054980257858403/50000000000000000000 : ℝ)+(109093565887949/800000000000000000 : ℝ) ≤ ((2653146871194668581/2654000000000000000 : ℝ)+(89968604379/53080000000000 : ℝ)*((881/6250 : ℝ)+(5721/50000 : ℝ)))^(1051/256 : ℝ) := by
    rw [show (2653146871194668581/2654000000000000000 : ℝ)+(89968604379/53080000000000 : ℝ)*((881/6250 : ℝ)+(5721/50000 : ℝ))=(62506963081763/62500000000000 : ℝ) by norm_num, show 1+(16054980257858403/50000000000000000000 : ℝ)+(109093565887949/800000000000000000 : ℝ)=(100045746656251710431/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16054980257858403/50000000000000000000 : ℝ) ≤ ((2653146871194668581/2654000000000000000 : ℝ)+2*(89968604379/53080000000000 : ℝ)*(881/6250 : ℝ))^(1051/256 : ℝ) := by
    rw [show (2653146871194668581/2654000000000000000 : ℝ)+2*(89968604379/53080000000000 : ℝ)*(881/6250 : ℝ)=(400062557444159/400000000000000 : ℝ) by norm_num, show 1+2*(16054980257858403/50000000000000000000 : ℝ)=(25016054980257858403/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2653146871194668581/2654000000000000000 : ℝ)*(X 1 0+X 2 0)+(89968604379/53080000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (5721/50000 : ℝ)) (hi := (881/6250 : ℝ)) (c := (2653146871194668581/2654000000000000000 : ℝ)) (alpha := (89968604379/53080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2653146871194668581/2654000000000000000 : ℝ)*(X 0 1+X 2 1)+(89968604379/53080000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (5721/50000 : ℝ)) (hi := (881/6250 : ℝ)) (c := (2653146871194668581/2654000000000000000 : ℝ)) (alpha := (89968604379/53080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2653146871194668581/2654000000000000000 : ℝ)*(X 0 2+X 1 2)+(89968604379/53080000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (5721/50000 : ℝ)) (hi := (881/6250 : ℝ)) (c := (2653146871194668581/2654000000000000000 : ℝ)) (alpha := (89968604379/53080000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2131990127/10000000000 : ℝ)*X 0 0+(5391685823/10000000000 : ℝ)*X 0 1+(5266853761/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344442739/10000000000 : ℝ)*X 1 0+(-1097644651/5000000000 : ℝ)*X 1 1+(5266853761/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344442739/10000000000 : ℝ)*X 2 0+(5266853759/10000000000 : ℝ)*X 2 1+(-274411163/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((217717557/500000000 : ℝ)*X 0 0+(4230153687/10000000000 : ℝ)*X 0 1+(2241056827/5000000000 : ℝ)*X 0 2+(217717557/500000000 : ℝ)*X 1 0+(4230153687/10000000000 : ℝ)*X 1 1+(2241056827/5000000000 : ℝ)*X 1 2+(217717557/500000000 : ℝ)*X 2 0+(4230153687/10000000000 : ℝ)*X 2 1+(2241056827/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1065997421/5000000000 : ℝ)*X 0 0+(5267168281/10000000000 : ℝ)*X 0 1+(2695685081/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656323893/5000000000 : ℝ)*X 1 0+(-1035386451/5000000000 : ℝ)*X 1 1+(2695685081/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656323893/5000000000 : ℝ)*X 2 0+(2695685081/5000000000 : ℝ)*X 2 1+(-1035386451/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2177180327/5000000000 : ℝ)*X 0 0+(179259153/400000000 : ℝ)*X 0 1+(2115395409/5000000000 : ℝ)*X 0 2+(2177180327/5000000000 : ℝ)*X 1 0+(179259153/400000000 : ℝ)*X 1 1+(2115395409/5000000000 : ℝ)*X 1 2+(2177180327/5000000000 : ℝ)*X 2 0+(179259153/400000000 : ℝ)*X 2 1+(2115395409/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2190214542982090246460667/1061600000000000000000000000000 : ℝ) := by norm_num
    linear_combination (81467039/20000000000000 : ℝ)*(base19) + (188703573/50000000000000 : ℝ)*(base23) + (127959/800000000000 : ℝ)*(lower2) + (54608977/100000000000000 : ℝ)*(upper3) + (28871367/100000000000000 : ℝ)*(upper5) + (47918725886869/800000000000 : ℝ)*(major0) + (47918725886869/800000000000 : ℝ)*(major1) + (47918725886869/800000000000 : ℝ)*(major2) + (4005387166068821/50000000000000 : ℝ)*(sp0) + (8010785022836657/100000000000000 : ℝ)*(sp1) + (4005392526382353/50000000000000 : ℝ)*(sp2) + (992222464300317/25000000000000 : ℝ)*(sp3) + (11098034211/100000000000000 : ℝ)*(sp4) + (3057786627/50000000000000 : ℝ)*(sp7) + (1984447986387261/50000000000000 : ℝ)*(f.failure) + (2002696357542963/25000000000000 : ℝ)*(f.sum) + (187232134177/530800000000000000000000000 : ℝ)*base66 + (27426632905880711/2123200000000000000000000000000 : ℝ)*base68 + (36473049800368711/2123200000000000000000000000000 : ℝ)*base70 + (19428686458324089/2123200000000000000000000000000 : ℝ)*base71 + (7321909761933/2654000000000000000000000000 : ℝ)*base74 + (21252111880674311/2123200000000000000000000000000 : ℝ)*base76 + (31805910135128889/2123200000000000000000000000000 : ℝ)*base77 + (27109255264951111/2123200000000000000000000000000 : ℝ)*base80 + (1244053331161/530800000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (3359777/500000000000000000000 : ℝ)*base89 + (3359777/500000000000000000000 : ℝ)*base91 + (3359777/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (435948001048964196968658039/66350000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (47332021/4000000000000 : ℝ)*(base19) + (1286335979/100000000000000 : ℝ)*(base23) + (26339107/20000000000000 : ℝ)*(upper3) + (23474853/50000000000000 : ℝ)*(lower4) + (33633781/25000000000000 : ℝ)*(upper5) + (6020214276823327/100000000000000 : ℝ)*(major0) + (6020214276823327/100000000000000 : ℝ)*(major1) + (6020214276823327/100000000000000 : ℝ)*(major2) + (33220031513/100000000000000 : ℝ)*(sp1) + (7133983593/20000000000000 : ℝ)*(sp2) + (2012851678540089/25000000000000 : ℝ)*(sp4) + (8051372310828319/100000000000000 : ℝ)*(sp5) + (8051369757906413/100000000000000 : ℝ)*(sp6) + (124656925639749/3125000000000 : ℝ)*(sp7) + (124656925639749/3125000000000 : ℝ)*(f.failure) + (2012851678540089/25000000000000 : ℝ)*(f.sum) + (15898578697653/2654000000000000000000000000 : ℝ)*base65 + (948248260907038987/265400000000000000000000000000000 : ℝ)*base67 + (1891919931263038987/265400000000000000000000000000000 : ℝ)*base69 + (2407500457591238987/265400000000000000000000000000000 : ℝ)*base71 + (7059090350789/2654000000000000000000000000 : ℝ)*base73 + (2655717139368438987/265400000000000000000000000000000 : ℝ)*base75 + (277911772146438987/265400000000000000000000000000000 : ℝ)*base77 + (417941049439961013/265400000000000000000000000000000 : ℝ)*base80 + (19587215071481/2654000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (288707/31250000000000000000 : ℝ)*base90 + (288707/31250000000000000000 : ℝ)*base92 + (288707/31250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1216_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (881/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5721/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11447/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1216_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1216_s8_0 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344430979/10000000000 : ℝ)*x 0 + (658362363/1250000000 : ℝ)*x 1 + (-2195245127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344430979/10000000000 : ℝ)^8409 ≤ (43681354695959/100000000000000 : ℝ)^6361 := by
    have hnat : (5344430979 : ℕ)^8409*100000000000000^6361 ≤ 43681354695959^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344430979 10000000000 43681354695959 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658362363/1250000000 : ℝ)^8409 ≤ (2677850314003/6250000000000 : ℝ)^6361 := by
    have hnat : (658362363 : ℕ)^8409*6250000000000^6361 ≤ 2677850314003^6361*1250000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658362363 1250000000 2677850314003 6250000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2195245127/10000000000 : ℝ)^8409 ≤ (1347304026293/10000000000000 : ℝ)^6361 := by
    have hnat : (2195245127 : ℕ)^8409*10000000000000^6361 ≤ 1347304026293^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2195245127 10000000000 1347304026293 10000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344430979/10000000000 : ℝ), (658362363/1250000000 : ℝ), (-2195245127/10000000000 : ℝ)] ![(43681354695959/100000000000000 : ℝ), (2677850314003/6250000000000 : ℝ), (1347304026293/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344430979/10000000000 : ℝ)|^8409 ≤ (43681354695959/100000000000000 : ℝ)^6361
        have hw : |(5344430979/10000000000 : ℝ)|=(5344430979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658362363/1250000000 : ℝ)|^8409 ≤ (2677850314003/6250000000000 : ℝ)^6361
        have hw : |(658362363/1250000000 : ℝ)|=(658362363/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2195245127/10000000000 : ℝ)|^8409 ≤ (1347304026293/10000000000000 : ℝ)^6361
        have hw : |(-2195245127/10000000000 : ℝ)|=(2195245127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s8_1 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2131998209/10000000000 : ℝ)*x 0 + (5267212941/10000000000 : ℝ)*x 1 + (2695661669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2131998209/10000000000 : ℝ)^8409 ≤ (2592457993431/20000000000000 : ℝ)^6361 := by
    have hnat : (2131998209 : ℕ)^8409*20000000000000^6361 ≤ 2592457993431^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2131998209 10000000000 2592457993431 20000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267212941/10000000000 : ℝ)^8409 ≤ (42848982212089/100000000000000 : ℝ)^6361 := by
    have hnat : (5267212941 : ℕ)^8409*100000000000000^6361 ≤ 42848982212089^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267212941 10000000000 42848982212089 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695661669/5000000000 : ℝ)^8409 ≤ (8837745560417/20000000000000 : ℝ)^6361 := by
    have hnat : (2695661669 : ℕ)^8409*20000000000000^6361 ≤ 8837745560417^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695661669 5000000000 8837745560417 20000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2131998209/10000000000 : ℝ), (5267212941/10000000000 : ℝ), (2695661669/5000000000 : ℝ)] ![(2592457993431/20000000000000 : ℝ), (42848982212089/100000000000000 : ℝ), (8837745560417/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2131998209/10000000000 : ℝ)|^8409 ≤ (2592457993431/20000000000000 : ℝ)^6361
        have hw : |(-2131998209/10000000000 : ℝ)|=(2131998209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267212941/10000000000 : ℝ)|^8409 ≤ (42848982212089/100000000000000 : ℝ)^6361
        have hw : |(5267212941/10000000000 : ℝ)|=(5267212941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695661669/5000000000 : ℝ)|^8409 ≤ (8837745560417/20000000000000 : ℝ)^6361
        have hw : |(2695661669/5000000000 : ℝ)|=(2695661669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s8_2 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312659529/10000000000 : ℝ)*x 0 + (-414164143/2000000000 : ℝ)*x 1 + (2695661669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312659529/10000000000 : ℝ)^8409 ≤ (8667680396827/20000000000000 : ℝ)^6361 := by
    have hnat : (5312659529 : ℕ)^8409*20000000000000^6361 ≤ 8667680396827^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312659529 10000000000 8667680396827 20000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (414164143/2000000000 : ℝ)^8409 ≤ (12472870199559/100000000000000 : ℝ)^6361 := by
    have hnat : (414164143 : ℕ)^8409*100000000000000^6361 ≤ 12472870199559^6361*2000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414164143 2000000000 12472870199559 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695661669/5000000000 : ℝ)^8409 ≤ (8837745560417/20000000000000 : ℝ)^6361 := by
    have hnat : (2695661669 : ℕ)^8409*20000000000000^6361 ≤ 8837745560417^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695661669 5000000000 8837745560417 20000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312659529/10000000000 : ℝ), (-414164143/2000000000 : ℝ), (2695661669/5000000000 : ℝ)] ![(8667680396827/20000000000000 : ℝ), (12472870199559/100000000000000 : ℝ), (8837745560417/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312659529/10000000000 : ℝ)|^8409 ≤ (8667680396827/20000000000000 : ℝ)^6361
        have hw : |(5312659529/10000000000 : ℝ)|=(5312659529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-414164143/2000000000 : ℝ)|^8409 ≤ (12472870199559/100000000000000 : ℝ)^6361
        have hw : |(-414164143/2000000000 : ℝ)|=(414164143/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695661669/5000000000 : ℝ)|^8409 ≤ (8837745560417/20000000000000 : ℝ)^6361
        have hw : |(2695661669/5000000000 : ℝ)|=(2695661669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s8_3 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312659529/10000000000 : ℝ)*x 0 + (2695661669/5000000000 : ℝ)*x 1 + (-1035410357/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312659529/10000000000 : ℝ)^8409 ≤ (8667680396827/20000000000000 : ℝ)^6361 := by
    have hnat : (5312659529 : ℕ)^8409*20000000000000^6361 ≤ 8667680396827^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312659529 10000000000 8667680396827 20000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695661669/5000000000 : ℝ)^8409 ≤ (8837745560417/20000000000000 : ℝ)^6361 := by
    have hnat : (2695661669 : ℕ)^8409*20000000000000^6361 ≤ 8837745560417^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695661669 5000000000 8837745560417 20000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1035410357/5000000000 : ℝ)^8409 ≤ (12472870191597/100000000000000 : ℝ)^6361 := by
    have hnat : (1035410357 : ℕ)^8409*100000000000000^6361 ≤ 12472870191597^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035410357 5000000000 12472870191597 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312659529/10000000000 : ℝ), (2695661669/5000000000 : ℝ), (-1035410357/5000000000 : ℝ)] ![(8667680396827/20000000000000 : ℝ), (8837745560417/20000000000000 : ℝ), (12472870191597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312659529/10000000000 : ℝ)|^8409 ≤ (8667680396827/20000000000000 : ℝ)^6361
        have hw : |(5312659529/10000000000 : ℝ)|=(5312659529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695661669/5000000000 : ℝ)|^8409 ≤ (8837745560417/20000000000000 : ℝ)^6361
        have hw : |(2695661669/5000000000 : ℝ)|=(2695661669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1035410357/5000000000 : ℝ)|^8409 ≤ (12472870191597/100000000000000 : ℝ)^6361
        have hw : |(-1035410357/5000000000 : ℝ)|=(1035410357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s8_4 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (435436297/1000000000 : ℝ)*x 0 + (2240693099/5000000000 : ℝ)*x 1 + (4230882839/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435436297/1000000000 : ℝ)^8409 ≤ (33317476121389/100000000000000 : ℝ)^6361 := by
    have hnat : (435436297 : ℕ)^8409*100000000000000^6361 ≤ 33317476121389^6361*1000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435436297 1000000000 33317476121389 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2240693099/5000000000 : ℝ)^8409 ≤ (4326039005587/12500000000000 : ℝ)^6361 := by
    have hnat : (2240693099 : ℕ)^8409*12500000000000^6361 ≤ 4326039005587^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240693099 5000000000 4326039005587 12500000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4230882839/10000000000 : ℝ)^8409 ≤ (16037105909261/50000000000000 : ℝ)^6361 := by
    have hnat : (4230882839 : ℕ)^8409*50000000000000^6361 ≤ 16037105909261^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230882839 10000000000 16037105909261 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435436297/1000000000 : ℝ), (2240693099/5000000000 : ℝ), (4230882839/10000000000 : ℝ)] ![(33317476121389/100000000000000 : ℝ), (4326039005587/12500000000000 : ℝ), (16037105909261/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435436297/1000000000 : ℝ)|^8409 ≤ (33317476121389/100000000000000 : ℝ)^6361
        have hw : |(435436297/1000000000 : ℝ)|=(435436297/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2240693099/5000000000 : ℝ)|^8409 ≤ (4326039005587/12500000000000 : ℝ)^6361
        have hw : |(2240693099/5000000000 : ℝ)|=(2240693099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4230882839/10000000000 : ℝ)|^8409 ≤ (16037105909261/50000000000000 : ℝ)^6361
        have hw : |(4230882839/10000000000 : ℝ)|=(4230882839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1216_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11447/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11447/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1409/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14091/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11447/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14091/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11447/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14091/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11447/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14091/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11447/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14091/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11447/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14091/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11447/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11447/100000 : ℝ) ^ (1051/256 : ℝ) ≤ (273223540895677/2000000000000000000 : ℝ) := by
    have hpowers : (11447/100000 : ℝ)^1051 ≤ (273223540895677/2000000000000000000 : ℝ)^256 := by
      have hnat : (11447 : ℕ)^1051*2000000000000000000^256 ≤ 273223540895677^256*100000^1051 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11447 100000 273223540895677 2000000000000000000 1051 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11447/100000 : ℝ)) (X := (273223540895677/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14091/100000 : ℝ) ^ (1051/256 : ℝ) ≤ (400790325422951/1250000000000000000 : ℝ) := by
    have hpowers : (14091/100000 : ℝ)^1051 ≤ (400790325422951/1250000000000000000 : ℝ)^256 := by
      have hnat : (14091 : ℕ)^1051*1250000000000000000^256 ≤ 400790325422951^256*100000^1051 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14091 100000 400790325422951 1250000000000000000 1051 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14091/100000 : ℝ)) (X := (400790325422951/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000273223540895677/1000000000000000000 : ℝ) ≤ (10000665442433403/10000000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (1000273223540895677/1000000000000000000 : ℝ)^256 ≤ (10000665442433403/10000000000000000 : ℝ)^1051 := by
      have hnat : (1000273223540895677 : ℕ)^256*10000000000000000^1051 ≤ 10000665442433403^1051*1000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000273223540895677 1000000000000000000 10000665442433403 10000000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000665442433403/10000000000000000 : ℝ)) (X := (1000273223540895677/1000000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004572440307861993/10000000000000000000 : ℝ) ≤ (5000556775616099/5000000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (10004572440307861993/10000000000000000000 : ℝ)^256 ≤ (5000556775616099/5000000000000000 : ℝ)^1051 := by
      have hnat : (10004572440307861993 : ℕ)^256*5000000000000000^1051 ≤ 5000556775616099^1051*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004572440307861993 10000000000000000000 5000556775616099 5000000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000556775616099/5000000000000000 : ℝ)) (X := (10004572440307861993/10000000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (625400790325422951/625000000000000000 : ℝ) ≤ (10001561660030993/10000000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (625400790325422951/625000000000000000 : ℝ)^256 ≤ (10001561660030993/10000000000000000 : ℝ)^1051 := by
      have hnat : (625400790325422951 : ℕ)^256*10000000000000000^1051 ≤ 10001561660030993^1051*625000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625400790325422951 625000000000000000 10001561660030993 10000000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001561660030993/10000000000000000 : ℝ)) (X := (625400790325422951/625000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(273223540895677/2000000000000000000 : ℝ) ≤ ((13215750213477152401/13220000000000000000 : ℝ)+2*(89621759759/52880000000000 : ℝ)*(11447/100000 : ℝ))^(1051/256 : ℝ) := by
    rw [show (13215750213477152401/13220000000000000000 : ℝ)+2*(89621759759/52880000000000 : ℝ)*(11447/100000 : ℝ)=(10000665442433403/10000000000000000 : ℝ) by norm_num, show 1+2*(273223540895677/2000000000000000000 : ℝ)=(1000273223540895677/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(400790325422951/1250000000000000000 : ℝ)+(273223540895677/2000000000000000000 : ℝ) ≤ ((13215750213477152401/13220000000000000000 : ℝ)+(89621759759/52880000000000 : ℝ)*((14091/100000 : ℝ)+(11447/100000 : ℝ)))^(1051/256 : ℝ) := by
    rw [show (13215750213477152401/13220000000000000000 : ℝ)+(89621759759/52880000000000 : ℝ)*((14091/100000 : ℝ)+(11447/100000 : ℝ))=(5000556775616099/5000000000000000 : ℝ) by norm_num, show 1+(400790325422951/1250000000000000000 : ℝ)+(273223540895677/2000000000000000000 : ℝ)=(10004572440307861993/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(400790325422951/1250000000000000000 : ℝ) ≤ ((13215750213477152401/13220000000000000000 : ℝ)+2*(89621759759/52880000000000 : ℝ)*(14091/100000 : ℝ))^(1051/256 : ℝ) := by
    rw [show (13215750213477152401/13220000000000000000 : ℝ)+2*(89621759759/52880000000000 : ℝ)*(14091/100000 : ℝ)=(10001561660030993/10000000000000000 : ℝ) by norm_num, show 1+2*(400790325422951/1250000000000000000 : ℝ)=(625400790325422951/625000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13215750213477152401/13220000000000000000 : ℝ)*(X 1 0+X 2 0)+(89621759759/52880000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (11447/100000 : ℝ)) (hi := (14091/100000 : ℝ)) (c := (13215750213477152401/13220000000000000000 : ℝ)) (alpha := (89621759759/52880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13215750213477152401/13220000000000000000 : ℝ)*(X 0 1+X 2 1)+(89621759759/52880000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (11447/100000 : ℝ)) (hi := (14091/100000 : ℝ)) (c := (13215750213477152401/13220000000000000000 : ℝ)) (alpha := (89621759759/52880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13215750213477152401/13220000000000000000 : ℝ)*(X 0 2+X 1 2)+(89621759759/52880000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (11447/100000 : ℝ)) (hi := (14091/100000 : ℝ)) (c := (13215750213477152401/13220000000000000000 : ℝ)) (alpha := (89621759759/52880000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5344430979/10000000000 : ℝ)*X 2 0+(658362363/1250000000 : ℝ)*X 2 1+(-2195245127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s8_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-2131998209/10000000000 : ℝ)*X 0 0+(5267212941/10000000000 : ℝ)*X 0 1+(2695661669/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s8_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5312659529/10000000000 : ℝ)*X 1 0+(-414164143/2000000000 : ℝ)*X 1 1+(2695661669/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s8_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5312659529/10000000000 : ℝ)*X 2 0+(2695661669/5000000000 : ℝ)*X 2 1+(-1035410357/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s8_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((435436297/1000000000 : ℝ)*X 0 0+(2240693099/5000000000 : ℝ)*X 0 1+(4230882839/10000000000 : ℝ)*X 0 2+(435436297/1000000000 : ℝ)*X 1 0+(2240693099/5000000000 : ℝ)*X 1 1+(4230882839/10000000000 : ℝ)*X 1 2+(435436297/1000000000 : ℝ)*X 2 0+(2240693099/5000000000 : ℝ)*X 2 1+(4230882839/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s8_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1072679356255200281094594831/165250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1168978443/100000000000000 : ℝ)*(base19) + (636518341/50000000000000 : ℝ)*(base23) + (204047019/50000000000000 : ℝ)*(lower1) + (130650339/100000000000000 : ℝ)*(upper3) + (23608553/50000000000000 : ℝ)*(lower4) + (6633423/5000000000000 : ℝ)*(upper5) + (3012313641821523/50000000000000 : ℝ)*(major0) + (3012313641821523/50000000000000 : ℝ)*(major1) + (3012313641821523/50000000000000 : ℝ)*(major2) + (2538597439/100000000000000 : ℝ)*(sp0) + (8057308651858831/100000000000000 : ℝ)*(sp1) + (2014326870720097/25000000000000 : ℝ)*(sp2) + (805730484022471/10000000000000 : ℝ)*(sp3) + (3991945699052181/100000000000000 : ℝ)*(sp4) + (3991945699052181/100000000000000 : ℝ)*(f.failure) + (8057308651858831/100000000000000 : ℝ)*(f.sum) + (1414895549811/264400000000000000000000000 : ℝ)*base65 + (28054185662203176723/661000000000000000000000000000000 : ℝ)*base67 + (3740166619795176723/661000000000000000000000000000000 : ℝ)*base69 + (6806640371389823277/661000000000000000000000000000000 : ℝ)*base72 + (5162526620361/1322000000000000000000000000 : ℝ)*base73 + (70742301226969176723/661000000000000000000000000000000 : ℝ)*base75 + (2044805922951176723/661000000000000000000000000000000 : ℝ)*base77 + (7559710874438176723/661000000000000000000000000000000 : ℝ)*base79 + (75697579101/264400000000000000000000000 : ℝ)*base81 + (3591783/1000000000000000000000 : ℝ)*base90 + (3591783/1000000000000000000000 : ℝ)*base92 + (3591783/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1216_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14091/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11447/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11447/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1216_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1216_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11419/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11447/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1216_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1216_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1216_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14119/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11419/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11447/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1409/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1216_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
