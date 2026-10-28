-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1247_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:22:13.944891+00:00
-- url     : https://prove2.me/submissions/4202f569-b17b-4992-9ca5-a81694d3df85

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
theorem support_rectangle_w1247_s3_0 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2114857573/10000000000 : ℝ)*x 0 + (5419219661/10000000000 : ℝ)*x 1 + (5241005059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114857573/10000000000 : ℝ)^1055 ≤ (2571170371911/20000000000000 : ℝ)^799 := by
    have hnat : (2114857573 : ℕ)^1055*20000000000000^799 ≤ 2571170371911^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114857573 10000000000 2571170371911 20000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419219661/10000000000 : ℝ)^1055 ≤ (44533820880263/100000000000000 : ℝ)^799 := by
    have hnat : (5419219661 : ℕ)^1055*100000000000000^799 ≤ 44533820880263^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419219661 10000000000 44533820880263 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241005059/10000000000 : ℝ)^1055 ≤ (8522065448223/20000000000000 : ℝ)^799 := by
    have hnat : (5241005059 : ℕ)^1055*20000000000000^799 ≤ 8522065448223^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241005059 10000000000 8522065448223 20000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2114857573/10000000000 : ℝ), (5419219661/10000000000 : ℝ), (5241005059/10000000000 : ℝ)] ![(2571170371911/20000000000000 : ℝ), (44533820880263/100000000000000 : ℝ), (8522065448223/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2114857573/10000000000 : ℝ)|^1055 ≤ (2571170371911/20000000000000 : ℝ)^799
        have hw : |(-2114857573/10000000000 : ℝ)|=(2114857573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419219661/10000000000 : ℝ)|^1055 ≤ (44533820880263/100000000000000 : ℝ)^799
        have hw : |(5419219661/10000000000 : ℝ)|=(5419219661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241005059/10000000000 : ℝ)|^1055 ≤ (8522065448223/20000000000000 : ℝ)^799
        have hw : |(5241005059/10000000000 : ℝ)|=(5241005059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s3_1 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (334461233/625000000 : ℝ)*x 0 + (-2205763447/10000000000 : ℝ)*x 1 + (2620502583/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334461233/625000000 : ℝ)^1055 ≤ (4379918865453/10000000000000 : ℝ)^799 := by
    have hnat : (334461233 : ℕ)^1055*10000000000000^799 ≤ 4379918865453^799*625000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334461233 625000000 4379918865453 10000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2205763447/10000000000 : ℝ)^1055 ≤ (1359048294213/10000000000000 : ℝ)^799 := by
    have hnat : (2205763447 : ℕ)^1055*10000000000000^799 ≤ 1359048294213^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205763447 10000000000 1359048294213 10000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620502583/5000000000 : ℝ)^1055 ≤ (4261032838977/10000000000000 : ℝ)^799 := by
    have hnat : (2620502583 : ℕ)^1055*10000000000000^799 ≤ 4261032838977^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620502583 5000000000 4261032838977 10000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334461233/625000000 : ℝ), (-2205763447/10000000000 : ℝ), (2620502583/5000000000 : ℝ)] ![(4379918865453/10000000000000 : ℝ), (1359048294213/10000000000000 : ℝ), (4261032838977/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334461233/625000000 : ℝ)|^1055 ≤ (4379918865453/10000000000000 : ℝ)^799
        have hw : |(334461233/625000000 : ℝ)|=(334461233/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2205763447/10000000000 : ℝ)|^1055 ≤ (1359048294213/10000000000000 : ℝ)^799
        have hw : |(-2205763447/10000000000 : ℝ)|=(2205763447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620502583/5000000000 : ℝ)|^1055 ≤ (4261032838977/10000000000000 : ℝ)^799
        have hw : |(2620502583/5000000000 : ℝ)|=(2620502583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s3_2 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5351379667/10000000000 : ℝ)*x 0 + (2620502807/5000000000 : ℝ)*x 1 + (-2205762937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351379667/10000000000 : ℝ)^1055 ≤ (21899593997651/50000000000000 : ℝ)^799 := by
    have hnat : (5351379667 : ℕ)^1055*50000000000000^799 ≤ 21899593997651^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351379667 10000000000 21899593997651 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620502807/5000000000 : ℝ)^1055 ≤ (21305166599547/50000000000000 : ℝ)^799 := by
    have hnat : (2620502807 : ℕ)^1055*50000000000000^799 ≤ 21305166599547^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620502807 5000000000 21305166599547 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2205762937/10000000000 : ℝ)^1055 ≤ (271809575861/2000000000000 : ℝ)^799 := by
    have hnat : (2205762937 : ℕ)^1055*2000000000000^799 ≤ 271809575861^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205762937 10000000000 271809575861 2000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351379667/10000000000 : ℝ), (2620502807/5000000000 : ℝ), (-2205762937/10000000000 : ℝ)] ![(21899593997651/50000000000000 : ℝ), (21305166599547/50000000000000 : ℝ), (271809575861/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351379667/10000000000 : ℝ)|^1055 ≤ (21899593997651/50000000000000 : ℝ)^799
        have hw : |(5351379667/10000000000 : ℝ)|=(5351379667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620502807/5000000000 : ℝ)|^1055 ≤ (21305166599547/50000000000000 : ℝ)^799
        have hw : |(2620502807/5000000000 : ℝ)|=(2620502807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2205762937/10000000000 : ℝ)|^1055 ≤ (271809575861/2000000000000 : ℝ)^799
        have hw : |(-2205762937/10000000000 : ℝ)|=(2205762937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s3_3 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2174206761/5000000000 : ℝ)*x 0 + (4171131257/10000000000 : ℝ)*x 1 + (453299969/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174206761/5000000000 : ℝ)^1055 ≤ (2081286533423/6250000000000 : ℝ)^799 := by
    have hnat : (2174206761 : ℕ)^1055*6250000000000^799 ≤ 2081286533423^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174206761 5000000000 2081286533423 6250000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171131257/10000000000 : ℝ)^1055 ≤ (6303953450323/20000000000000 : ℝ)^799 := by
    have hnat : (4171131257 : ℕ)^1055*20000000000000^799 ≤ 6303953450323^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171131257 10000000000 6303953450323 20000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (453299969/1000000000 : ℝ)^1055 ≤ (17589824102097/50000000000000 : ℝ)^799 := by
    have hnat : (453299969 : ℕ)^1055*50000000000000^799 ≤ 17589824102097^799*1000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453299969 1000000000 17589824102097 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2174206761/5000000000 : ℝ), (4171131257/10000000000 : ℝ), (453299969/1000000000 : ℝ)] ![(2081286533423/6250000000000 : ℝ), (6303953450323/20000000000000 : ℝ), (17589824102097/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2174206761/5000000000 : ℝ)|^1055 ≤ (2081286533423/6250000000000 : ℝ)^799
        have hw : |(2174206761/5000000000 : ℝ)|=(2174206761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171131257/10000000000 : ℝ)|^1055 ≤ (6303953450323/20000000000000 : ℝ)^799
        have hw : |(4171131257/10000000000 : ℝ)|=(4171131257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(453299969/1000000000 : ℝ)|^1055 ≤ (17589824102097/50000000000000 : ℝ)^799
        have hw : |(453299969/1000000000 : ℝ)|=(453299969/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s3_4 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2114871717/10000000000 : ℝ)*x 0 + (5241650971/10000000000 : ℝ)*x 1 + (169330317/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2114871717/10000000000 : ℝ)^1055 ≤ (2571193077257/20000000000000 : ℝ)^799 := by
    have hnat : (2114871717 : ℕ)^1055*20000000000000^799 ≤ 2571193077257^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114871717 10000000000 2571193077257 20000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241650971/10000000000 : ℝ)^1055 ≤ (42617261305951/100000000000000 : ℝ)^799 := by
    have hnat : (5241650971 : ℕ)^1055*100000000000000^799 ≤ 42617261305951^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241650971 10000000000 42617261305951 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169330317/312500000 : ℝ)^1055 ≤ (8905354656637/20000000000000 : ℝ)^799 := by
    have hnat : (169330317 : ℕ)^1055*20000000000000^799 ≤ 8905354656637^799*312500000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169330317 312500000 8905354656637 20000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2114871717/10000000000 : ℝ), (5241650971/10000000000 : ℝ), (169330317/312500000 : ℝ)] ![(2571193077257/20000000000000 : ℝ), (42617261305951/100000000000000 : ℝ), (8905354656637/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2114871717/10000000000 : ℝ)|^1055 ≤ (2571193077257/20000000000000 : ℝ)^799
        have hw : |(-2114871717/10000000000 : ℝ)|=(2114871717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241650971/10000000000 : ℝ)|^1055 ≤ (42617261305951/100000000000000 : ℝ)^799
        have hw : |(5241650971/10000000000 : ℝ)|=(5241650971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169330317/312500000 : ℝ)|^1055 ≤ (8905354656637/20000000000000 : ℝ)^799
        have hw : |(169330317/312500000 : ℝ)|=(169330317/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s3_5 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305897509/10000000000 : ℝ)*x 0 + (-405639679/2000000000 : ℝ)*x 1 + (2709285183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305897509/10000000000 : ℝ)^1055 ≤ (43308331920231/100000000000000 : ℝ)^799 := by
    have hnat : (5305897509 : ℕ)^1055*100000000000000^799 ≤ 43308331920231^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305897509 10000000000 43308331920231 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (405639679/2000000000 : ℝ)^1055 ≤ (12164892377893/100000000000000 : ℝ)^799 := by
    have hnat : (405639679 : ℕ)^1055*100000000000000^799 ≤ 12164892377893^799*2000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405639679 2000000000 12164892377893 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2709285183/5000000000 : ℝ)^1055 ≤ (22263387845977/50000000000000 : ℝ)^799 := by
    have hnat : (2709285183 : ℕ)^1055*50000000000000^799 ≤ 22263387845977^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709285183 5000000000 22263387845977 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305897509/10000000000 : ℝ), (-405639679/2000000000 : ℝ), (2709285183/5000000000 : ℝ)] ![(43308331920231/100000000000000 : ℝ), (12164892377893/100000000000000 : ℝ), (22263387845977/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305897509/10000000000 : ℝ)|^1055 ≤ (43308331920231/100000000000000 : ℝ)^799
        have hw : |(5305897509/10000000000 : ℝ)|=(5305897509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-405639679/2000000000 : ℝ)|^1055 ≤ (12164892377893/100000000000000 : ℝ)^799
        have hw : |(-405639679/2000000000 : ℝ)|=(405639679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2709285183/5000000000 : ℝ)|^1055 ≤ (22263387845977/50000000000000 : ℝ)^799
        have hw : |(2709285183/5000000000 : ℝ)|=(2709285183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s3_6 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2652948801/5000000000 : ℝ)*x 0 + (216742811/400000000 : ℝ)*x 1 + (-2028198393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652948801/5000000000 : ℝ)^1055 ≤ (43308332922539/100000000000000 : ℝ)^799 := by
    have hnat : (2652948801 : ℕ)^1055*100000000000000^799 ≤ 43308332922539^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652948801 5000000000 43308332922539 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (216742811/400000000 : ℝ)^1055 ≤ (695730854759/1562500000000 : ℝ)^799 := by
    have hnat : (216742811 : ℕ)^1055*1562500000000^799 ≤ 695730854759^799*400000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216742811 400000000 695730854759 1562500000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2028198393/10000000000 : ℝ)^1055 ≤ (12164892362053/100000000000000 : ℝ)^799 := by
    have hnat : (2028198393 : ℕ)^1055*100000000000000^799 ≤ 12164892362053^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2028198393 10000000000 12164892362053 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652948801/5000000000 : ℝ), (216742811/400000000 : ℝ), (-2028198393/10000000000 : ℝ)] ![(43308332922539/100000000000000 : ℝ), (695730854759/1562500000000 : ℝ), (12164892362053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652948801/5000000000 : ℝ)|^1055 ≤ (43308332922539/100000000000000 : ℝ)^799
        have hw : |(2652948801/5000000000 : ℝ)|=(2652948801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(216742811/400000000 : ℝ)|^1055 ≤ (695730854759/1562500000000 : ℝ)^799
        have hw : |(216742811/400000000 : ℝ)|=(216742811/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2028198393/10000000000 : ℝ)|^1055 ≤ (12164892362053/100000000000000 : ℝ)^799
        have hw : |(-2028198393/10000000000 : ℝ)|=(2028198393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s3_7 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (543555223/1250000000 : ℝ)*x 0 + (1132922209/2500000000 : ℝ)*x 1 + (260778047/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543555223/1250000000 : ℝ)^1055 ≤ (4162608789199/12500000000000 : ℝ)^799 := by
    have hnat : (543555223 : ℕ)^1055*12500000000000^799 ≤ 4162608789199^799*1250000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543555223 1250000000 4162608789199 12500000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1132922209/2500000000 : ℝ)^1055 ≤ (8791554012369/25000000000000 : ℝ)^799 := by
    have hnat : (1132922209 : ℕ)^1055*25000000000000^799 ≤ 8791554012369^799*2500000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132922209 2500000000 8791554012369 25000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260778047/625000000 : ℝ)^1055 ≤ (31532913619311/100000000000000 : ℝ)^799 := by
    have hnat : (260778047 : ℕ)^1055*100000000000000^799 ≤ 31532913619311^799*625000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260778047 625000000 31532913619311 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543555223/1250000000 : ℝ), (1132922209/2500000000 : ℝ), (260778047/625000000 : ℝ)] ![(4162608789199/12500000000000 : ℝ), (8791554012369/25000000000000 : ℝ), (31532913619311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543555223/1250000000 : ℝ)|^1055 ≤ (4162608789199/12500000000000 : ℝ)^799
        have hw : |(543555223/1250000000 : ℝ)|=(543555223/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1132922209/2500000000 : ℝ)|^1055 ≤ (8791554012369/25000000000000 : ℝ)^799
        have hw : |(1132922209/2500000000 : ℝ)|=(1132922209/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(260778047/625000000 : ℝ)|^1055 ≤ (31532913619311/100000000000000 : ℝ)^799
        have hw : |(260778047/625000000 : ℝ)|=(260778047/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1247_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151526459/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1621/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (119/1250 : ℝ)*pair X i i ≤ pair X i h) :
    (2731/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1837/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1621/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (119/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1621/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (119/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1621/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (119/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1621/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (119/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1621/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (119/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1621/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (119/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (119/1250 : ℝ) ^ (8439/2048 : ℝ) ≤ (386585749901797/6250000000000000000 : ℝ) := by
    have hpowers : (119/1250 : ℝ)^8439 ≤ (386585749901797/6250000000000000000 : ℝ)^2048 := by
      have hnat : (119 : ℕ)^8439*6250000000000000000^2048 ≤ 386585749901797^2048*1250^8439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        119 1250 386585749901797 6250000000000000000 8439 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (119/1250 : ℝ)) (X := (386585749901797/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1621/10000 : ℝ) ^ (8439/2048 : ℝ) ≤ (3465034689563957/6250000000000000000 : ℝ) := by
    have hpowers : (1621/10000 : ℝ)^8439 ≤ (3465034689563957/6250000000000000000 : ℝ)^2048 := by
      have hnat : (1621 : ℕ)^8439*6250000000000000000^2048 ≤ 3465034689563957^2048*10000^8439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1621 10000 3465034689563957 6250000000000000000 8439 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1621/10000 : ℝ)) (X := (3465034689563957/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125386585749901797/3125000000000000000 : ℝ) ≤ (10000300202595257/10000000000000000 : ℝ) ^ (8439/2048 : ℝ) := by
    have hpowers : (3125386585749901797/3125000000000000000 : ℝ)^2048 ≤ (10000300202595257/10000000000000000 : ℝ)^8439 := by
      have hnat : (3125386585749901797 : ℕ)^2048*10000000000000000^8439 ≤ 10000300202595257^8439*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125386585749901797 3125000000000000000 10000300202595257 10000000000000000 2048 8439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000300202595257/10000000000000000 : ℝ)) (X := (3125386585749901797/3125000000000000000 : ℝ)) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126925810219732877/3125000000000000000 : ℝ) ≤ (625093450392427/625000000000000 : ℝ) ^ (8439/2048 : ℝ) := by
    have hpowers : (3126925810219732877/3125000000000000000 : ℝ)^2048 ≤ (625093450392427/625000000000000 : ℝ)^8439 := by
      have hnat : (3126925810219732877 : ℕ)^2048*625000000000000^8439 ≤ 625093450392427^8439*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126925810219732877 3125000000000000000 625093450392427 625000000000000 2048 8439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625093450392427/625000000000000 : ℝ)) (X := (3126925810219732877/3125000000000000000 : ℝ)) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (3128465034689563957/3125000000000000000 : ℝ) ≤ (10002690209962407/10000000000000000 : ℝ) ^ (8439/2048 : ℝ) := by
    have hpowers : (3128465034689563957/3125000000000000000 : ℝ)^2048 ≤ (10002690209962407/10000000000000000 : ℝ)^8439 := by
      have hnat : (3128465034689563957 : ℕ)^2048*10000000000000000^8439 ≤ 10002690209962407^8439*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3128465034689563957 3125000000000000000 10002690209962407 10000000000000000 2048 8439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002690209962407/10000000000000000 : ℝ)) (X := (3128465034689563957/3125000000000000000 : ℝ)) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(386585749901797/6250000000000000000 : ℝ) ≤ ((6687925548522700133/6690000000000000000 : ℝ)+2*(47800147343/26760000000000 : ℝ)*(119/1250 : ℝ))^(8439/2048 : ℝ) := by
    rw [show (6687925548522700133/6690000000000000000 : ℝ)+2*(47800147343/26760000000000 : ℝ)*(119/1250 : ℝ)=(10000300202595257/10000000000000000 : ℝ) by norm_num, show 1+2*(386585749901797/6250000000000000000 : ℝ)=(3125386585749901797/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3465034689563957/6250000000000000000 : ℝ)+(386585749901797/6250000000000000000 : ℝ) ≤ ((6687925548522700133/6690000000000000000 : ℝ)+(47800147343/26760000000000 : ℝ)*((1621/10000 : ℝ)+(119/1250 : ℝ)))^(8439/2048 : ℝ) := by
    rw [show (6687925548522700133/6690000000000000000 : ℝ)+(47800147343/26760000000000 : ℝ)*((1621/10000 : ℝ)+(119/1250 : ℝ))=(625093450392427/625000000000000 : ℝ) by norm_num, show 1+(3465034689563957/6250000000000000000 : ℝ)+(386585749901797/6250000000000000000 : ℝ)=(3126925810219732877/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3465034689563957/6250000000000000000 : ℝ) ≤ ((6687925548522700133/6690000000000000000 : ℝ)+2*(47800147343/26760000000000 : ℝ)*(1621/10000 : ℝ))^(8439/2048 : ℝ) := by
    rw [show (6687925548522700133/6690000000000000000 : ℝ)+2*(47800147343/26760000000000 : ℝ)*(1621/10000 : ℝ)=(10002690209962407/10000000000000000 : ℝ) by norm_num, show 1+2*(3465034689563957/6250000000000000000 : ℝ)=(3128465034689563957/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6687925548522700133/6690000000000000000 : ℝ)*(X 1 0+X 2 0)+(47800147343/26760000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8439/2048 : ℝ)) (lo := (119/1250 : ℝ)) (hi := (1621/10000 : ℝ)) (c := (6687925548522700133/6690000000000000000 : ℝ)) (alpha := (47800147343/26760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6687925548522700133/6690000000000000000 : ℝ)*(X 0 1+X 2 1)+(47800147343/26760000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8439/2048 : ℝ)) (lo := (119/1250 : ℝ)) (hi := (1621/10000 : ℝ)) (c := (6687925548522700133/6690000000000000000 : ℝ)) (alpha := (47800147343/26760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6687925548522700133/6690000000000000000 : ℝ)*(X 0 2+X 1 2)+(47800147343/26760000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8439/2048 : ℝ)) (lo := (119/1250 : ℝ)) (hi := (1621/10000 : ℝ)) (c := (6687925548522700133/6690000000000000000 : ℝ)) (alpha := (47800147343/26760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2114857573/10000000000 : ℝ)*X 0 0+(5419219661/10000000000 : ℝ)*X 0 1+(5241005059/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334461233/625000000 : ℝ)*X 1 0+(-2205763447/10000000000 : ℝ)*X 1 1+(2620502583/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351379667/10000000000 : ℝ)*X 2 0+(2620502807/5000000000 : ℝ)*X 2 1+(-2205762937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2174206761/5000000000 : ℝ)*X 0 0+(4171131257/10000000000 : ℝ)*X 0 1+(453299969/1000000000 : ℝ)*X 0 2+(2174206761/5000000000 : ℝ)*X 1 0+(4171131257/10000000000 : ℝ)*X 1 1+(453299969/1000000000 : ℝ)*X 1 2+(2174206761/5000000000 : ℝ)*X 2 0+(4171131257/10000000000 : ℝ)*X 2 1+(453299969/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2114871717/10000000000 : ℝ)*X 0 0+(5241650971/10000000000 : ℝ)*X 0 1+(169330317/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305897509/10000000000 : ℝ)*X 1 0+(-405639679/2000000000 : ℝ)*X 1 1+(2709285183/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652948801/5000000000 : ℝ)*X 2 0+(216742811/400000000 : ℝ)*X 2 1+(-2028198393/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((543555223/1250000000 : ℝ)*X 0 0+(1132922209/2500000000 : ℝ)*X 0 1+(260778047/625000000 : ℝ)*X 0 2+(543555223/1250000000 : ℝ)*X 1 0+(1132922209/2500000000 : ℝ)*X 1 1+(260778047/625000000 : ℝ)*X 1 2+(543555223/1250000000 : ℝ)*X 2 0+(1132922209/2500000000 : ℝ)*X 2 1+(260778047/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (187999457101102391631248443/27875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (416278659/50000000000000 : ℝ)*(base19) + (44843677/10000000000000 : ℝ)*(base23) + (102626523/50000000000000 : ℝ)*(lower2) + (29459937/100000000000000 : ℝ)*(upper5) + (2093681830833071/50000000000000 : ℝ)*(major0) + (2093681830833071/50000000000000 : ℝ)*(major1) + (2093681830833071/50000000000000 : ℝ)*(major2) + (5611240162862397/100000000000000 : ℝ)*(sp0) + (1402816256337853/25000000000000 : ℝ)*(sp1) + (561127286828101/10000000000000 : ℝ)*(sp2) + (172715247278947/6250000000000 : ℝ)*(sp3) + (33153855383/100000000000000 : ℝ)*(sp4) + (149176181/2000000000000 : ℝ)*(sp5) + (9825338839/100000000000000 : ℝ)*(sp7) + (2763453781801991/100000000000000 : ℝ)*(f.failure) + (280563665835889/5000000000000 : ℝ)*(f.sum) + (2306949283379/669000000000000000000000000 : ℝ)*base66 + (2946469043940251557/334500000000000000000000000000000 : ℝ)*base68 + (3741406823812751557/334500000000000000000000000000000 : ℝ)*base70 + (5701031295456251557/334500000000000000000000000000000 : ℝ)*base72 + (1641069570727/669000000000000000000000000 : ℝ)*base73 + (1006753960449251557/334500000000000000000000000000000 : ℝ)*base76 + (4162863579954251557/334500000000000000000000000000000 : ℝ)*base78 + (3280557590924748443/334500000000000000000000000000000 : ℝ)*base79 + (478084187669/669000000000000000000000000 : ℝ)*base82 + (135379869/10000000000000000000000 : ℝ)*base89 + (135379869/10000000000000000000000 : ℝ)*base91 + (135379869/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (16500791502229025077515897/2787500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (607351873/100000000000000 : ℝ)*(base19) + (451659963/50000000000000 : ℝ)*(base23) + (89975857/50000000000000 : ℝ)*(upper3) + (73173917/100000000000000 : ℝ)*(lower4) + (53419417/100000000000000 : ℝ)*(upper5) + (105449367292803/2500000000000 : ℝ)*(major0) + (105449367292803/2500000000000 : ℝ)*(major1) + (105449367292803/2500000000000 : ℝ)*(major2) + (12602874373/100000000000000 : ℝ)*(sp1) + (9742086951/50000000000000 : ℝ)*(sp2) + (2826146816059573/50000000000000 : ℝ)*(sp4) + (56522804218929/1000000000000 : ℝ)*(sp5) + (5652273244625317/100000000000000 : ℝ)*(sp6) + (13918277769931/500000000000 : ℝ)*(sp7) + (13918277769931/500000000000 : ℝ)*(f.failure) + (2826146816059573/50000000000000 : ℝ)*(f.sum) + (299416977773/111500000000000000000000000 : ℝ)*base65 + (55035753832019067/5575000000000000000000000000000 : ℝ)*base68 + (104909399760369067/5575000000000000000000000000000 : ℝ)*base70 + (17986664721869067/5575000000000000000000000000000 : ℝ)*base72 + (395918037773/223000000000000000000000000 : ℝ)*base73 + (143607901524419067/5575000000000000000000000000000 : ℝ)*base76 + (45504551540669067/5575000000000000000000000000000 : ℝ)*base78 + (67993989678294067/5575000000000000000000000000000 : ℝ)*base80 + (53692115559/8920000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1104329/50000000000000000000 : ℝ)*base89 + (1104329/50000000000000000000 : ℝ)*base91 + (1104329/50000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1247_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151526459/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1621/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (119/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2731/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1837/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1247_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1247_s4_0 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-264640037/1250000000 : ℝ)*x 0 + (5397291461/10000000000 : ℝ)*x 1 + (1315362553/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264640037/1250000000 : ℝ)^1055 ≤ (2574803336929/20000000000000 : ℝ)^799 := by
    have hnat : (264640037 : ℕ)^1055*20000000000000^799 ≤ 2574803336929^799*1250000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264640037 1250000000 2574803336929 20000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397291461/10000000000 : ℝ)^1055 ≤ (22148019161297/50000000000000 : ℝ)^799 := by
    have hnat : (5397291461 : ℕ)^1055*50000000000000^799 ≤ 22148019161297^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397291461 10000000000 22148019161297 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315362553/2500000000 : ℝ)^1055 ≤ (21414972491089/50000000000000 : ℝ)^799 := by
    have hnat : (1315362553 : ℕ)^1055*50000000000000^799 ≤ 21414972491089^799*2500000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315362553 2500000000 21414972491089 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-264640037/1250000000 : ℝ), (5397291461/10000000000 : ℝ), (1315362553/2500000000 : ℝ)] ![(2574803336929/20000000000000 : ℝ), (22148019161297/50000000000000 : ℝ), (21414972491089/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-264640037/1250000000 : ℝ)|^1055 ≤ (2574803336929/20000000000000 : ℝ)^799
        have hw : |(-264640037/1250000000 : ℝ)|=(264640037/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397291461/10000000000 : ℝ)|^1055 ≤ (22148019161297/50000000000000 : ℝ)^799
        have hw : |(5397291461/10000000000 : ℝ)|=(5397291461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315362553/2500000000 : ℝ)|^1055 ≤ (21414972491089/50000000000000 : ℝ)^799
        have hw : |(1315362553/2500000000 : ℝ)|=(1315362553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s4_1 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5345848739/10000000000 : ℝ)*x 0 + (-273260791/1250000000 : ℝ)*x 1 + (2630725107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345848739/10000000000 : ℝ)^1055 ≤ (21869712521127/50000000000000 : ℝ)^799 := by
    have hnat : (5345848739 : ℕ)^1055*50000000000000^799 ≤ 21869712521127^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345848739 10000000000 21869712521127 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273260791/1250000000 : ℝ)^1055 ≤ (13430629943573/100000000000000 : ℝ)^799 := by
    have hnat : (273260791 : ℕ)^1055*100000000000000^799 ≤ 13430629943573^799*1250000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273260791 1250000000 13430629943573 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630725107/5000000000 : ℝ)^1055 ≤ (1713197800147/4000000000000 : ℝ)^799 := by
    have hnat : (2630725107 : ℕ)^1055*4000000000000^799 ≤ 1713197800147^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630725107 5000000000 1713197800147 4000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345848739/10000000000 : ℝ), (-273260791/1250000000 : ℝ), (2630725107/5000000000 : ℝ)] ![(21869712521127/50000000000000 : ℝ), (13430629943573/100000000000000 : ℝ), (1713197800147/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345848739/10000000000 : ℝ)|^1055 ≤ (21869712521127/50000000000000 : ℝ)^799
        have hw : |(5345848739/10000000000 : ℝ)|=(5345848739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-273260791/1250000000 : ℝ)|^1055 ≤ (13430629943573/100000000000000 : ℝ)^799
        have hw : |(-273260791/1250000000 : ℝ)|=(273260791/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630725107/5000000000 : ℝ)|^1055 ≤ (1713197800147/4000000000000 : ℝ)^799
        have hw : |(2630725107/5000000000 : ℝ)|=(2630725107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s4_2 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5345848819/10000000000 : ℝ)*x 0 + (526145011/1000000000 : ℝ)*x 1 + (-2186086359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345848819/10000000000 : ℝ)^1055 ≤ (43739425906529/100000000000000 : ℝ)^799 := by
    have hnat : (5345848819 : ℕ)^1055*100000000000000^799 ≤ 43739425906529^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345848819 10000000000 43739425906529 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526145011/1000000000 : ℝ)^1055 ≤ (42829943885831/100000000000000 : ℝ)^799 := by
    have hnat : (526145011 : ℕ)^1055*100000000000000^799 ≤ 42829943885831^799*1000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526145011 1000000000 42829943885831 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2186086359/10000000000 : ℝ)^1055 ≤ (13430630195049/100000000000000 : ℝ)^799 := by
    have hnat : (2186086359 : ℕ)^1055*100000000000000^799 ≤ 13430630195049^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186086359 10000000000 13430630195049 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345848819/10000000000 : ℝ), (526145011/1000000000 : ℝ), (-2186086359/10000000000 : ℝ)] ![(43739425906529/100000000000000 : ℝ), (42829943885831/100000000000000 : ℝ), (13430630195049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345848819/10000000000 : ℝ)|^1055 ≤ (43739425906529/100000000000000 : ℝ)^799
        have hw : |(5345848819/10000000000 : ℝ)|=(5345848819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526145011/1000000000 : ℝ)|^1055 ≤ (42829943885831/100000000000000 : ℝ)^799
        have hw : |(526145011/1000000000 : ℝ)|=(526145011/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2186086359/10000000000 : ℝ)|^1055 ≤ (13430630195049/100000000000000 : ℝ)^799
        have hw : |(-2186086359/10000000000 : ℝ)|=(2186086359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s4_3 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4349769737/10000000000 : ℝ)*x 0 + (2106988831/5000000000 : ℝ)*x 1 + (561225927/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349769737/10000000000 : ℝ)^1055 ≤ (6662859787763/20000000000000 : ℝ)^799 := by
    have hnat : (4349769737 : ℕ)^1055*20000000000000^799 ≤ 6662859787763^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349769737 10000000000 6662859787763 20000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2106988831/5000000000 : ℝ)^1055 ≤ (15973991013269/50000000000000 : ℝ)^799 := by
    have hnat : (2106988831 : ℕ)^1055*50000000000000^799 ≤ 15973991013269^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2106988831 5000000000 15973991013269 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (561225927/1250000000 : ℝ)^1055 ≤ (34737719025623/100000000000000 : ℝ)^799 := by
    have hnat : (561225927 : ℕ)^1055*100000000000000^799 ≤ 34737719025623^799*1250000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561225927 1250000000 34737719025623 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349769737/10000000000 : ℝ), (2106988831/5000000000 : ℝ), (561225927/1250000000 : ℝ)] ![(6662859787763/20000000000000 : ℝ), (15973991013269/50000000000000 : ℝ), (34737719025623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349769737/10000000000 : ℝ)|^1055 ≤ (6662859787763/20000000000000 : ℝ)^799
        have hw : |(4349769737/10000000000 : ℝ)|=(4349769737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2106988831/5000000000 : ℝ)|^1055 ≤ (15973991013269/50000000000000 : ℝ)^799
        have hw : |(2106988831/5000000000 : ℝ)|=(2106988831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(561225927/1250000000 : ℝ)|^1055 ≤ (34737719025623/100000000000000 : ℝ)^799
        have hw : |(561225927/1250000000 : ℝ)|=(561225927/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s4_4 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-264640793/1250000000 : ℝ)*x 0 + (2630912931/5000000000 : ℝ)*x 1 + (674614297/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264640793/1250000000 : ℝ)^1055 ≤ (6437032622743/50000000000000 : ℝ)^799 := by
    have hnat : (264640793 : ℕ)^1055*50000000000000^799 ≤ 6437032622743^799*1250000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264640793 1250000000 6437032622743 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2630912931/5000000000 : ℝ)^1055 ≤ (334640489853/781250000000 : ℝ)^799 := by
    have hnat : (2630912931 : ℕ)^1055*781250000000^799 ≤ 334640489853^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630912931 5000000000 334640489853 781250000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674614297/1250000000 : ℝ)^1055 ≤ (692061750523/1562500000000 : ℝ)^799 := by
    have hnat : (674614297 : ℕ)^1055*1562500000000^799 ≤ 692061750523^799*1250000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674614297 1250000000 692061750523 1562500000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-264640793/1250000000 : ℝ), (2630912931/5000000000 : ℝ), (674614297/1250000000 : ℝ)] ![(6437032622743/50000000000000 : ℝ), (334640489853/781250000000 : ℝ), (692061750523/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-264640793/1250000000 : ℝ)|^1055 ≤ (6437032622743/50000000000000 : ℝ)^799
        have hw : |(-264640793/1250000000 : ℝ)|=(264640793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2630912931/5000000000 : ℝ)|^1055 ≤ (334640489853/781250000000 : ℝ)^799
        have hw : |(2630912931/5000000000 : ℝ)|=(2630912931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674614297/1250000000 : ℝ)|^1055 ≤ (692061750523/1562500000000 : ℝ)^799
        have hw : |(674614297/1250000000 : ℝ)|=(674614297/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s4_5 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1062235657/2000000000 : ℝ)*x 0 + (-410124413/2000000000 : ℝ)*x 1 + (2698457217/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062235657/2000000000 : ℝ)^1055 ≤ (1084131364713/2500000000000 : ℝ)^799 := by
    have hnat : (1062235657 : ℕ)^1055*2500000000000^799 ≤ 1084131364713^799*2000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062235657 2000000000 1084131364713 2500000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (410124413/2000000000 : ℝ)^1055 ≤ (12342792736489/100000000000000 : ℝ)^799 := by
    have hnat : (410124413 : ℕ)^1055*100000000000000^799 ≤ 12342792736489^799*2000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410124413 2000000000 12342792736489 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698457217/5000000000 : ℝ)^1055 ≤ (1384123520687/3125000000000 : ℝ)^799 := by
    have hnat : (2698457217 : ℕ)^1055*3125000000000^799 ≤ 1384123520687^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698457217 5000000000 1384123520687 3125000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062235657/2000000000 : ℝ), (-410124413/2000000000 : ℝ), (2698457217/5000000000 : ℝ)] ![(1084131364713/2500000000000 : ℝ), (12342792736489/100000000000000 : ℝ), (1384123520687/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062235657/2000000000 : ℝ)|^1055 ≤ (1084131364713/2500000000000 : ℝ)^799
        have hw : |(1062235657/2000000000 : ℝ)|=(1062235657/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-410124413/2000000000 : ℝ)|^1055 ≤ (12342792736489/100000000000000 : ℝ)^799
        have hw : |(-410124413/2000000000 : ℝ)|=(410124413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698457217/5000000000 : ℝ)|^1055 ≤ (1384123520687/3125000000000 : ℝ)^799
        have hw : |(2698457217/5000000000 : ℝ)|=(2698457217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s4_6 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5311178363/10000000000 : ℝ)*x 0 + (5396914317/10000000000 : ℝ)*x 1 + (-1025311059/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311178363/10000000000 : ℝ)^1055 ≤ (21682627714717/50000000000000 : ℝ)^799 := by
    have hnat : (5311178363 : ℕ)^1055*50000000000000^799 ≤ 21682627714717^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311178363 10000000000 21682627714717 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396914317/10000000000 : ℝ)^1055 ≤ (354335611153/800000000000 : ℝ)^799 := by
    have hnat : (5396914317 : ℕ)^1055*800000000000^799 ≤ 354335611153^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396914317 10000000000 354335611153 800000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1025311059/5000000000 : ℝ)^1055 ≤ (1234279315771/10000000000000 : ℝ)^799 := by
    have hnat : (1025311059 : ℕ)^1055*10000000000000^799 ≤ 1234279315771^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025311059 5000000000 1234279315771 10000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311178363/10000000000 : ℝ), (5396914317/10000000000 : ℝ), (-1025311059/5000000000 : ℝ)] ![(21682627714717/50000000000000 : ℝ), (354335611153/800000000000 : ℝ), (1234279315771/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311178363/10000000000 : ℝ)|^1055 ≤ (21682627714717/50000000000000 : ℝ)^799
        have hw : |(5311178363/10000000000 : ℝ)|=(5311178363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396914317/10000000000 : ℝ)|^1055 ≤ (354335611153/800000000000 : ℝ)^799
        have hw : |(5396914317/10000000000 : ℝ)|=(5396914317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1025311059/5000000000 : ℝ)|^1055 ≤ (1234279315771/10000000000000 : ℝ)^799
        have hw : |(-1025311059/5000000000 : ℝ)|=(1025311059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s4_7 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4349782161/10000000000 : ℝ)*x 0 + (56113057/125000000 : ℝ)*x 1 + (4214743579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349782161/10000000000 : ℝ)^1055 ≤ (8328606144979/25000000000000 : ℝ)^799 := by
    have hnat : (4349782161 : ℕ)^1055*25000000000000^799 ≤ 8328606144979^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349782161 10000000000 8328606144979 25000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (56113057/125000000 : ℝ)^1055 ≤ (34729925929913/100000000000000 : ℝ)^799 := by
    have hnat : (56113057 : ℕ)^1055*100000000000000^799 ≤ 34729925929913^799*125000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56113057 125000000 34729925929913 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4214743579/10000000000 : ℝ)^1055 ≤ (31955649481551/100000000000000 : ℝ)^799 := by
    have hnat : (4214743579 : ℕ)^1055*100000000000000^799 ≤ 31955649481551^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4214743579 10000000000 31955649481551 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349782161/10000000000 : ℝ), (56113057/125000000 : ℝ), (4214743579/10000000000 : ℝ)] ![(8328606144979/25000000000000 : ℝ), (34729925929913/100000000000000 : ℝ), (31955649481551/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349782161/10000000000 : ℝ)|^1055 ≤ (8328606144979/25000000000000 : ℝ)^799
        have hw : |(4349782161/10000000000 : ℝ)|=(4349782161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(56113057/125000000 : ℝ)|^1055 ≤ (34729925929913/100000000000000 : ℝ)^799
        have hw : |(56113057/125000000 : ℝ)|=(56113057/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4214743579/10000000000 : ℝ)|^1055 ≤ (31955649481551/100000000000000 : ℝ)^799
        have hw : |(4214743579/10000000000 : ℝ)|=(4214743579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1247_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151526459/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1837/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2731/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (71/625 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14237/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1837/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2731/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1837/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2731/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1837/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2731/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1837/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2731/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1837/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2731/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1837/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2731/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2731/25000 : ℝ) ^ (8439/2048 : ℝ) ≤ (10903108628383187/100000000000000000000 : ℝ) := by
    have hpowers : (2731/25000 : ℝ)^8439 ≤ (10903108628383187/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2731 : ℕ)^8439*100000000000000000000^2048 ≤ 10903108628383187^2048*25000^8439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2731 25000 10903108628383187 100000000000000000000 8439 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2731/25000 : ℝ)) (X := (10903108628383187/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1837/12500 : ℝ) ^ (8439/2048 : ℝ) ≤ (2313322877692059/6250000000000000000 : ℝ) := by
    have hpowers : (1837/12500 : ℝ)^8439 ≤ (2313322877692059/6250000000000000000 : ℝ)^2048 := by
      have hnat : (1837 : ℕ)^8439*6250000000000000000^2048 ≤ 2313322877692059^2048*12500^8439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1837 12500 2313322877692059 6250000000000000000 8439 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1837/12500 : ℝ)) (X := (2313322877692059/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010903108628383187/50000000000000000000 : ℝ) ≤ (5000264577828287/5000000000000000 : ℝ) ^ (8439/2048 : ℝ) := by
    have hpowers : (50010903108628383187/50000000000000000000 : ℝ)^2048 ≤ (5000264577828287/5000000000000000 : ℝ)^8439 := by
      have hnat : (50010903108628383187 : ℕ)^2048*5000000000000000^8439 ≤ 5000264577828287^8439*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010903108628383187 50000000000000000000 5000264577828287 5000000000000000 2048 8439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000264577828287/5000000000000000 : ℝ)) (X := (50010903108628383187/50000000000000000000 : ℝ)) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047916274671456131/100000000000000000000 : ℝ) ≤ (2500290658639783/2500000000000000 : ℝ) ^ (8439/2048 : ℝ) := by
    have hpowers : (100047916274671456131/100000000000000000000 : ℝ)^2048 ≤ (2500290658639783/2500000000000000 : ℝ)^8439 := by
      have hnat : (100047916274671456131 : ℕ)^2048*2500000000000000^8439 ≤ 2500290658639783^8439*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047916274671456131 100000000000000000000 2500290658639783 2500000000000000 2048 8439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500290658639783/2500000000000000 : ℝ)) (X := (100047916274671456131/100000000000000000000 : ℝ)) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (3127313322877692059/3125000000000000000 : ℝ) ≤ (1000179611346169/1000000000000000 : ℝ) ^ (8439/2048 : ℝ) := by
    have hpowers : (3127313322877692059/3125000000000000000 : ℝ)^2048 ≤ (1000179611346169/1000000000000000 : ℝ)^8439 := by
      have hnat : (3127313322877692059 : ℕ)^2048*1000000000000000^8439 ≤ 1000179611346169^8439*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3127313322877692059 3125000000000000000 1000179611346169 1000000000000000 2048 8439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000179611346169/1000000000000000 : ℝ)) (X := (3127313322877692059/3125000000000000000 : ℝ)) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10903108628383187/100000000000000000000 : ℝ) ≤ ((4713519466009188743/4715000000000000000 : ℝ)+2*(316739451279/188600000000000 : ℝ)*(2731/25000 : ℝ))^(8439/2048 : ℝ) := by
    rw [show (4713519466009188743/4715000000000000000 : ℝ)+2*(316739451279/188600000000000 : ℝ)*(2731/25000 : ℝ)=(5000264577828287/5000000000000000 : ℝ) by norm_num, show 1+2*(10903108628383187/100000000000000000000 : ℝ)=(50010903108628383187/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2313322877692059/6250000000000000000 : ℝ)+(10903108628383187/100000000000000000000 : ℝ) ≤ ((4713519466009188743/4715000000000000000 : ℝ)+(316739451279/188600000000000 : ℝ)*((1837/12500 : ℝ)+(2731/25000 : ℝ)))^(8439/2048 : ℝ) := by
    rw [show (4713519466009188743/4715000000000000000 : ℝ)+(316739451279/188600000000000 : ℝ)*((1837/12500 : ℝ)+(2731/25000 : ℝ))=(2500290658639783/2500000000000000 : ℝ) by norm_num, show 1+(2313322877692059/6250000000000000000 : ℝ)+(10903108628383187/100000000000000000000 : ℝ)=(100047916274671456131/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2313322877692059/6250000000000000000 : ℝ) ≤ ((4713519466009188743/4715000000000000000 : ℝ)+2*(316739451279/188600000000000 : ℝ)*(1837/12500 : ℝ))^(8439/2048 : ℝ) := by
    rw [show (4713519466009188743/4715000000000000000 : ℝ)+2*(316739451279/188600000000000 : ℝ)*(1837/12500 : ℝ)=(1000179611346169/1000000000000000 : ℝ) by norm_num, show 1+2*(2313322877692059/6250000000000000000 : ℝ)=(3127313322877692059/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4713519466009188743/4715000000000000000 : ℝ)*(X 1 0+X 2 0)+(316739451279/188600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8439/2048 : ℝ)) (lo := (2731/25000 : ℝ)) (hi := (1837/12500 : ℝ)) (c := (4713519466009188743/4715000000000000000 : ℝ)) (alpha := (316739451279/188600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4713519466009188743/4715000000000000000 : ℝ)*(X 0 1+X 2 1)+(316739451279/188600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8439/2048 : ℝ)) (lo := (2731/25000 : ℝ)) (hi := (1837/12500 : ℝ)) (c := (4713519466009188743/4715000000000000000 : ℝ)) (alpha := (316739451279/188600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4713519466009188743/4715000000000000000 : ℝ)*(X 0 2+X 1 2)+(316739451279/188600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8439/2048 : ℝ)) (lo := (2731/25000 : ℝ)) (hi := (1837/12500 : ℝ)) (c := (4713519466009188743/4715000000000000000 : ℝ)) (alpha := (316739451279/188600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-264640037/1250000000 : ℝ)*X 0 0+(5397291461/10000000000 : ℝ)*X 0 1+(1315362553/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345848739/10000000000 : ℝ)*X 1 0+(-273260791/1250000000 : ℝ)*X 1 1+(2630725107/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345848819/10000000000 : ℝ)*X 2 0+(526145011/1000000000 : ℝ)*X 2 1+(-2186086359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4349769737/10000000000 : ℝ)*X 0 0+(2106988831/5000000000 : ℝ)*X 0 1+(561225927/1250000000 : ℝ)*X 0 2+(4349769737/10000000000 : ℝ)*X 1 0+(2106988831/5000000000 : ℝ)*X 1 1+(561225927/1250000000 : ℝ)*X 1 2+(4349769737/10000000000 : ℝ)*X 2 0+(2106988831/5000000000 : ℝ)*X 2 1+(561225927/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-264640793/1250000000 : ℝ)*X 0 0+(2630912931/5000000000 : ℝ)*X 0 1+(674614297/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062235657/2000000000 : ℝ)*X 1 0+(-410124413/2000000000 : ℝ)*X 1 1+(2698457217/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5311178363/10000000000 : ℝ)*X 2 0+(5396914317/10000000000 : ℝ)*X 2 1+(-1025311059/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4349782161/10000000000 : ℝ)*X 0 0+(56113057/125000000 : ℝ)*X 0 1+(4214743579/10000000000 : ℝ)*X 0 2+(4349782161/10000000000 : ℝ)*X 1 0+(56113057/125000000 : ℝ)*X 1 1+(4214743579/10000000000 : ℝ)*X 1 2+(4349782161/10000000000 : ℝ)*X 2 0+(56113057/125000000 : ℝ)*X 2 1+(4214743579/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1358092703411205991965647667/235750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1246013741/100000000000000 : ℝ)*(base19) + (252590113/20000000000000 : ℝ)*(base23) + (41284807/20000000000000 : ℝ)*(upper3) + (24919281/50000000000000 : ℝ)*(upper4) + (14032003/12500000000000 : ℝ)*(upper5) + (5493524228253623/100000000000000 : ℝ)*(major0) + (5493524228253623/100000000000000 : ℝ)*(major1) + (5493524228253623/100000000000000 : ℝ)*(major2) + (736156438330447/10000000000000 : ℝ)*(sp0) + (460099474586549/6250000000000 : ℝ)*(sp1) + (7361591576447961/100000000000000 : ℝ)*(sp2) + (453179831239629/12500000000000 : ℝ)*(sp3) + (3557011757/12500000000000 : ℝ)*(sp4) + (838758363/5000000000000 : ℝ)*(sp7) + (3625455425084291/100000000000000 : ℝ)*(f.failure) + (3680796419699263/50000000000000 : ℝ)*(f.sum) + (46393284918017/9430000000000000000000000000 : ℝ)*base65 + (167342518416990889/471500000000000000000000000000000 : ℝ)*base67 + (2552023274656009111/471500000000000000000000000000000 : ℝ)*base70 + (1701704743404009111/471500000000000000000000000000000 : ℝ)*base72 + (21507170044057/9430000000000000000000000000 : ℝ)*base73 + (4904962777123990889/471500000000000000000000000000000 : ℝ)*base75 + (7472214395438509111/471500000000000000000000000000000 : ℝ)*base78 + (11881047280695009111/471500000000000000000000000000000 : ℝ)*base80 + (25938730450027/9430000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (91755569/10000000000000000000000 : ℝ)*base89 + (91755569/10000000000000000000000 : ℝ)*base91 + (91755569/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (42601848905268543700587/9430000000000000000000000000 : ℝ) := by norm_num
    linear_combination (228064727/25000000000000 : ℝ)*(base19) + (503124089/50000000000000 : ℝ)*(base23) + (3427159/50000000000000 : ℝ)*(upper2) + (68975233/100000000000000 : ℝ)*(upper3) + (25602773/20000000000000 : ℝ)*(upper5) + (5524093483942453/100000000000000 : ℝ)*(major0) + (5524093483942453/100000000000000 : ℝ)*(major1) + (5524093483942453/100000000000000 : ℝ)*(major2) + (29076325583/100000000000000 : ℝ)*(sp1) + (24843648499/100000000000000 : ℝ)*(sp2) + (1850639297261219/25000000000000 : ℝ)*(sp4) + (1480505440092077/20000000000000 : ℝ)*(sp5) + (7402531339148199/100000000000000 : ℝ)*(sp6) + (5696296294141/156250000000 : ℝ)*(sp7) + (5696296294141/156250000000 : ℝ)*(f.failure) + (1850639297261219/25000000000000 : ℝ)*(f.sum) + (42817628806107/9430000000000000000000000000 : ℝ)*base65 + (428386295895918421/471500000000000000000000000000000 : ℝ)*base68 + (1750759953588081579/471500000000000000000000000000000 : ℝ)*base69 + (3632067648769081579/471500000000000000000000000000000 : ℝ)*base71 + (17731802723457/9430000000000000000000000000 : ℝ)*base73 + (13934717526845918421/471500000000000000000000000000000 : ℝ)*base76 + (821568669415081579/471500000000000000000000000000000 : ℝ)*base77 + (2322574770857418421/471500000000000000000000000000000 : ℝ)*base80 + (61460144329477/9430000000000000000000000000 : ℝ)*base81 + (104531/15625000000000000000 : ℝ)*base90 + (104531/15625000000000000000 : ℝ)*base92 + (104531/15625000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1247_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151526459/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1837/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2731/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (71/625 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1247_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1247_s5_0 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2117561777/10000000000 : ℝ)*x 0 + (1078457661/2000000000 : ℝ)*x 1 + (5266163169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2117561777/10000000000 : ℝ)^1055 ≤ (3219390389527/25000000000000 : ℝ)^799 := by
    have hnat : (2117561777 : ℕ)^1055*25000000000000^799 ≤ 3219390389527^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117561777 10000000000 3219390389527 25000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078457661/2000000000 : ℝ)^1055 ≤ (44241828969071/100000000000000 : ℝ)^799 := by
    have hnat : (1078457661 : ℕ)^1055*100000000000000^799 ≤ 44241828969071^799*2000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078457661 2000000000 44241828969071 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266163169/10000000000 : ℝ)^1055 ≤ (2144030472663/5000000000000 : ℝ)^799 := by
    have hnat : (5266163169 : ℕ)^1055*5000000000000^799 ≤ 2144030472663^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266163169 10000000000 2144030472663 5000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2117561777/10000000000 : ℝ), (1078457661/2000000000 : ℝ), (5266163169/10000000000 : ℝ)] ![(3219390389527/25000000000000 : ℝ), (44241828969071/100000000000000 : ℝ), (2144030472663/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2117561777/10000000000 : ℝ)|^1055 ≤ (3219390389527/25000000000000 : ℝ)^799
        have hw : |(-2117561777/10000000000 : ℝ)|=(2117561777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078457661/2000000000 : ℝ)|^1055 ≤ (44241828969071/100000000000000 : ℝ)^799
        have hw : |(1078457661/2000000000 : ℝ)|=(1078457661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266163169/10000000000 : ℝ)|^1055 ≤ (2144030472663/5000000000000 : ℝ)^799
        have hw : |(5266163169/10000000000 : ℝ)|=(5266163169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s5_1 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344582383/10000000000 : ℝ)*x 0 + (-436305139/2000000000 : ℝ)*x 1 + (2633081589/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344582383/10000000000 : ℝ)^1055 ≤ (43725744559779/100000000000000 : ℝ)^799 := by
    have hnat : (5344582383 : ℕ)^1055*100000000000000^799 ≤ 43725744559779^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344582383 10000000000 43725744559779 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (436305139/2000000000 : ℝ)^1055 ≤ (3348411469687/25000000000000 : ℝ)^799 := by
    have hnat : (436305139 : ℕ)^1055*25000000000000^799 ≤ 3348411469687^799*2000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436305139 2000000000 3348411469687 25000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633081589/5000000000 : ℝ)^1055 ≤ (5360076193753/12500000000000 : ℝ)^799 := by
    have hnat : (2633081589 : ℕ)^1055*12500000000000^799 ≤ 5360076193753^799*5000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633081589 5000000000 5360076193753 12500000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344582383/10000000000 : ℝ), (-436305139/2000000000 : ℝ), (2633081589/5000000000 : ℝ)] ![(43725744559779/100000000000000 : ℝ), (3348411469687/25000000000000 : ℝ), (5360076193753/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344582383/10000000000 : ℝ)|^1055 ≤ (43725744559779/100000000000000 : ℝ)^799
        have hw : |(5344582383/10000000000 : ℝ)|=(5344582383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-436305139/2000000000 : ℝ)|^1055 ≤ (3348411469687/25000000000000 : ℝ)^799
        have hw : |(-436305139/2000000000 : ℝ)|=(436305139/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633081589/5000000000 : ℝ)|^1055 ≤ (5360076193753/12500000000000 : ℝ)^799
        have hw : |(2633081589/5000000000 : ℝ)|=(2633081589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s5_2 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5344582409/10000000000 : ℝ)*x 0 + (5266163183/10000000000 : ℝ)*x 1 + (-545381413/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344582409/10000000000 : ℝ)^1055 ≤ (43725744840647/100000000000000 : ℝ)^799 := by
    have hnat : (5344582409 : ℕ)^1055*100000000000000^799 ≤ 43725744840647^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344582409 10000000000 43725744840647 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266163183/10000000000 : ℝ)^1055 ≤ (21440304801891/50000000000000 : ℝ)^799 := by
    have hnat : (5266163183 : ℕ)^1055*50000000000000^799 ≤ 21440304801891^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266163183 10000000000 21440304801891 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (545381413/2500000000 : ℝ)^1055 ≤ (167420569127/1250000000000 : ℝ)^799 := by
    have hnat : (545381413 : ℕ)^1055*1250000000000^799 ≤ 167420569127^799*2500000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545381413 2500000000 167420569127 1250000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344582409/10000000000 : ℝ), (5266163183/10000000000 : ℝ), (-545381413/2500000000 : ℝ)] ![(43725744840647/100000000000000 : ℝ), (21440304801891/50000000000000 : ℝ), (167420569127/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344582409/10000000000 : ℝ)|^1055 ≤ (43725744840647/100000000000000 : ℝ)^799
        have hw : |(5344582409/10000000000 : ℝ)|=(5344582409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266163183/10000000000 : ℝ)|^1055 ≤ (21440304801891/50000000000000 : ℝ)^799
        have hw : |(5266163183/10000000000 : ℝ)|=(5266163183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-545381413/2500000000 : ℝ)|^1055 ≤ (167420569127/1250000000000 : ℝ)^799
        have hw : |(-545381413/2500000000 : ℝ)|=(545381413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s5_3 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4350029161/10000000000 : ℝ)*x 0 + (84476183/200000000 : ℝ)*x 1 + (4479909731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350029161/10000000000 : ℝ)^1055 ≤ (8329230614723/25000000000000 : ℝ)^799 := by
    have hnat : (4350029161 : ℕ)^1055*25000000000000^799 ≤ 8329230614723^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350029161 10000000000 8329230614723 25000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84476183/200000000 : ℝ)^1055 ≤ (8011609288629/25000000000000 : ℝ)^799 := by
    have hnat : (84476183 : ℕ)^1055*25000000000000^799 ≤ 8011609288629^799*200000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84476183 200000000 8011609288629 25000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4479909731/10000000000 : ℝ)^1055 ≤ (17318320189883/50000000000000 : ℝ)^799 := by
    have hnat : (4479909731 : ℕ)^1055*50000000000000^799 ≤ 17318320189883^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479909731 10000000000 17318320189883 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350029161/10000000000 : ℝ), (84476183/200000000 : ℝ), (4479909731/10000000000 : ℝ)] ![(8329230614723/25000000000000 : ℝ), (8011609288629/25000000000000 : ℝ), (17318320189883/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350029161/10000000000 : ℝ)|^1055 ≤ (8329230614723/25000000000000 : ℝ)^799
        have hw : |(4350029161/10000000000 : ℝ)|=(4350029161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84476183/200000000 : ℝ)|^1055 ≤ (8011609288629/25000000000000 : ℝ)^799
        have hw : |(84476183/200000000 : ℝ)|=(84476183/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4479909731/10000000000 : ℝ)|^1055 ≤ (17318320189883/50000000000000 : ℝ)^799
        have hw : |(4479909731/10000000000 : ℝ)|=(4479909731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s5_4 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-423513327/2000000000 : ℝ)*x 0 + (210659487/400000000 : ℝ)*x 1 + (269598157/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (423513327/2000000000 : ℝ)^1055 ≤ (3219400141689/25000000000000 : ℝ)^799 := by
    have hnat : (423513327 : ℕ)^1055*25000000000000^799 ≤ 3219400141689^799*2000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423513327 2000000000 3219400141689 25000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210659487/400000000 : ℝ)^1055 ≤ (8576818612849/20000000000000 : ℝ)^799 := by
    have hnat : (210659487 : ℕ)^1055*20000000000000^799 ≤ 8576818612849^799*400000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210659487 400000000 8576818612849 20000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269598157/500000000 : ℝ)^1055 ≤ (345611768387/781250000000 : ℝ)^799 := by
    have hnat : (269598157 : ℕ)^1055*781250000000^799 ≤ 345611768387^799*500000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269598157 500000000 345611768387 781250000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-423513327/2000000000 : ℝ), (210659487/400000000 : ℝ), (269598157/500000000 : ℝ)] ![(3219400141689/25000000000000 : ℝ), (8576818612849/20000000000000 : ℝ), (345611768387/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-423513327/2000000000 : ℝ)|^1055 ≤ (3219400141689/25000000000000 : ℝ)^799
        have hw : |(-423513327/2000000000 : ℝ)|=(423513327/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210659487/400000000 : ℝ)|^1055 ≤ (8576818612849/20000000000000 : ℝ)^799
        have hw : |(210659487/400000000 : ℝ)|=(210659487/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269598157/500000000 : ℝ)|^1055 ≤ (345611768387/781250000000 : ℝ)^799
        have hw : |(269598157/500000000 : ℝ)|=(269598157/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s5_5 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5312390337/10000000000 : ℝ)*x 0 + (-256965737/1250000000 : ℝ)*x 1 + (1078392621/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312390337/10000000000 : ℝ)^1055 ≤ (43378322128259/100000000000000 : ℝ)^799 := by
    have hnat : (5312390337 : ℕ)^1055*100000000000000^799 ≤ 43378322128259^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312390337 10000000000 43378322128259 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256965737/1250000000 : ℝ)^1055 ≤ (6191685936813/50000000000000 : ℝ)^799 := by
    have hnat : (256965737 : ℕ)^1055*50000000000000^799 ≤ 6191685936813^799*1250000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256965737 1250000000 6191685936813 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078392621/2000000000 : ℝ)^1055 ≤ (44238305974373/100000000000000 : ℝ)^799 := by
    have hnat : (1078392621 : ℕ)^1055*100000000000000^799 ≤ 44238305974373^799*2000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078392621 2000000000 44238305974373 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312390337/10000000000 : ℝ), (-256965737/1250000000 : ℝ), (1078392621/2000000000 : ℝ)] ![(43378322128259/100000000000000 : ℝ), (6191685936813/50000000000000 : ℝ), (44238305974373/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312390337/10000000000 : ℝ)|^1055 ≤ (43378322128259/100000000000000 : ℝ)^799
        have hw : |(5312390337/10000000000 : ℝ)|=(5312390337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-256965737/1250000000 : ℝ)|^1055 ≤ (6191685936813/50000000000000 : ℝ)^799
        have hw : |(-256965737/1250000000 : ℝ)|=(256965737/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078392621/2000000000 : ℝ)|^1055 ≤ (44238305974373/100000000000000 : ℝ)^799
        have hw : |(1078392621/2000000000 : ℝ)|=(1078392621/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s5_6 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1328097593/2500000000 : ℝ)*x 0 + (5391963127/10000000000 : ℝ)*x 1 + (-102786291/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328097593/2500000000 : ℝ)^1055 ≤ (43378322505619/100000000000000 : ℝ)^799 := by
    have hnat : (1328097593 : ℕ)^1055*100000000000000^799 ≤ 43378322505619^799*2500000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328097593 2500000000 43378322505619 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391963127/10000000000 : ℝ)^1055 ≤ (1382447069147/3125000000000 : ℝ)^799 := by
    have hnat : (5391963127 : ℕ)^1055*3125000000000^799 ≤ 1382447069147^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391963127 10000000000 1382447069147 3125000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (102786291/500000000 : ℝ)^1055 ≤ (12383371269131/100000000000000 : ℝ)^799 := by
    have hnat : (102786291 : ℕ)^1055*100000000000000^799 ≤ 12383371269131^799*500000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102786291 500000000 12383371269131 100000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328097593/2500000000 : ℝ), (5391963127/10000000000 : ℝ), (-102786291/500000000 : ℝ)] ![(43378322505619/100000000000000 : ℝ), (1382447069147/3125000000000 : ℝ), (12383371269131/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328097593/2500000000 : ℝ)|^1055 ≤ (43378322505619/100000000000000 : ℝ)^799
        have hw : |(1328097593/2500000000 : ℝ)|=(1328097593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391963127/10000000000 : ℝ)|^1055 ≤ (1382447069147/3125000000000 : ℝ)^799
        have hw : |(5391963127/10000000000 : ℝ)|=(5391963127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-102786291/500000000 : ℝ)|^1055 ≤ (12383371269131/100000000000000 : ℝ)^799
        have hw : |(-102786291/500000000 : ℝ)|=(102786291/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1247_s5_7 (p : ℝ) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ)) (x : Fin 3 → ℝ) :
    (543754911/1250000000 : ℝ)*x 0 + (4479251861/10000000000 : ℝ)*x 1 + (4224469289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (543754911/1250000000 : ℝ)^1055 ≤ (333170248729/1000000000000 : ℝ)^799 := by
    have hnat : (543754911 : ℕ)^1055*1000000000000^799 ≤ 333170248729^799*1250000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543754911 1250000000 333170248729 1000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4479251861/10000000000 : ℝ)^1055 ≤ (692598490269/2000000000000 : ℝ)^799 := by
    have hnat : (4479251861 : ℕ)^1055*2000000000000^799 ≤ 692598490269^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479251861 10000000000 692598490269 2000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4224469289/10000000000 : ℝ)^1055 ≤ (16026525297203/50000000000000 : ℝ)^799 := by
    have hnat : (4224469289 : ℕ)^1055*50000000000000^799 ≤ 16026525297203^799*10000000000^1055 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224469289 10000000000 16026525297203 50000000000000 1055 799 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1055/256 : ℝ)) 1055 799 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(543754911/1250000000 : ℝ), (4479251861/10000000000 : ℝ), (4224469289/10000000000 : ℝ)] ![(333170248729/1000000000000 : ℝ), (692598490269/2000000000000 : ℝ), (16026525297203/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(543754911/1250000000 : ℝ)|^1055 ≤ (333170248729/1000000000000 : ℝ)^799
        have hw : |(543754911/1250000000 : ℝ)|=(543754911/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4479251861/10000000000 : ℝ)|^1055 ≤ (692598490269/2000000000000 : ℝ)^799
        have hw : |(4479251861/10000000000 : ℝ)|=(4479251861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4224469289/10000000000 : ℝ)|^1055 ≤ (16026525297203/50000000000000 : ℝ)^799
        have hw : |(4224469289/10000000000 : ℝ)|=(4224469289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1247_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151526459/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (71/625 : ℝ)*pair X i i ≤ pair X i h) :
    (573/5000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3533/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (71/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (71/625 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (71/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14237/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (71/625 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (71/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14237/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (71/625 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (71/625 : ℝ) ^ (8439/2048 : ℝ) ≤ (6405555386066517/50000000000000000000 : ℝ) := by
    have hpowers : (71/625 : ℝ)^8439 ≤ (6405555386066517/50000000000000000000 : ℝ)^2048 := by
      have hnat : (71 : ℕ)^8439*50000000000000000000^2048 ≤ 6405555386066517^2048*625^8439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71 625 6405555386066517 50000000000000000000 8439 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (71/625 : ℝ)) (X := (6405555386066517/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14237/100000 : ℝ) ^ (8439/2048 : ℝ) ≤ (8119169132053077/25000000000000000000 : ℝ) := by
    have hpowers : (14237/100000 : ℝ)^8439 ≤ (8119169132053077/25000000000000000000 : ℝ)^2048 := by
      have hnat : (14237 : ℕ)^8439*25000000000000000000^2048 ≤ 8119169132053077^2048*100000^8439 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14237 100000 8119169132053077 25000000000000000000 8439 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14237/100000 : ℝ)) (X := (8119169132053077/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006405555386066517/25000000000000000000 : ℝ) ≤ (10000621746882213/10000000000000000 : ℝ) ^ (8439/2048 : ℝ) := by
    have hpowers : (25006405555386066517/25000000000000000000 : ℝ)^2048 ≤ (10000621746882213/10000000000000000 : ℝ)^8439 := by
      have hnat : (25006405555386066517 : ℕ)^2048*10000000000000000^8439 ≤ 10000621746882213^8439*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006405555386066517 25000000000000000000 10000621746882213 10000000000000000 2048 8439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000621746882213/10000000000000000 : ℝ)) (X := (25006405555386066517/25000000000000000000 : ℝ)) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50022643893650172671/50000000000000000000 : ℝ) ≤ (10001098868199761/10000000000000000 : ℝ) ^ (8439/2048 : ℝ) := by
    have hpowers : (50022643893650172671/50000000000000000000 : ℝ)^2048 ≤ (10001098868199761/10000000000000000 : ℝ)^8439 := by
      have hnat : (50022643893650172671 : ℕ)^2048*10000000000000000^8439 ≤ 10001098868199761^8439*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022643893650172671 50000000000000000000 10001098868199761 10000000000000000 2048 8439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001098868199761/10000000000000000 : ℝ)) (X := (50022643893650172671/50000000000000000000 : ℝ)) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508119169132053077/12500000000000000000 : ℝ) ≤ (10001575989517309/10000000000000000 : ℝ) ^ (8439/2048 : ℝ) := by
    have hpowers : (12508119169132053077/12500000000000000000 : ℝ)^2048 ≤ (10001575989517309/10000000000000000 : ℝ)^8439 := by
      have hnat : (12508119169132053077 : ℕ)^2048*10000000000000000^8439 ≤ 10001575989517309^8439*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508119169132053077 12500000000000000000 10001575989517309 10000000000000000 2048 8439 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001575989517309/10000000000000000 : ℝ)) (X := (12508119169132053077/12500000000000000000 : ℝ)) (by norm_num) 8439 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6405555386066517/50000000000000000000 : ℝ) ≤ ((28760948569445436241/28770000000000000000 : ℝ)+2*(119280329387/71925000000000 : ℝ)*(71/625 : ℝ))^(8439/2048 : ℝ) := by
    rw [show (28760948569445436241/28770000000000000000 : ℝ)+2*(119280329387/71925000000000 : ℝ)*(71/625 : ℝ)=(10000621746882213/10000000000000000 : ℝ) by norm_num, show 1+2*(6405555386066517/50000000000000000000 : ℝ)=(25006405555386066517/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8119169132053077/25000000000000000000 : ℝ)+(6405555386066517/50000000000000000000 : ℝ) ≤ ((28760948569445436241/28770000000000000000 : ℝ)+(119280329387/71925000000000 : ℝ)*((14237/100000 : ℝ)+(71/625 : ℝ)))^(8439/2048 : ℝ) := by
    rw [show (28760948569445436241/28770000000000000000 : ℝ)+(119280329387/71925000000000 : ℝ)*((14237/100000 : ℝ)+(71/625 : ℝ))=(10001098868199761/10000000000000000 : ℝ) by norm_num, show 1+(8119169132053077/25000000000000000000 : ℝ)+(6405555386066517/50000000000000000000 : ℝ)=(50022643893650172671/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8119169132053077/25000000000000000000 : ℝ) ≤ ((28760948569445436241/28770000000000000000 : ℝ)+2*(119280329387/71925000000000 : ℝ)*(14237/100000 : ℝ))^(8439/2048 : ℝ) := by
    rw [show (28760948569445436241/28770000000000000000 : ℝ)+2*(119280329387/71925000000000 : ℝ)*(14237/100000 : ℝ)=(10001575989517309/10000000000000000 : ℝ) by norm_num, show 1+2*(8119169132053077/25000000000000000000 : ℝ)=(12508119169132053077/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28760948569445436241/28770000000000000000 : ℝ)*(X 1 0+X 2 0)+(119280329387/71925000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8439/2048 : ℝ)) (lo := (71/625 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (28760948569445436241/28770000000000000000 : ℝ)) (alpha := (119280329387/71925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28760948569445436241/28770000000000000000 : ℝ)*(X 0 1+X 2 1)+(119280329387/71925000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8439/2048 : ℝ)) (lo := (71/625 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (28760948569445436241/28770000000000000000 : ℝ)) (alpha := (119280329387/71925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28760948569445436241/28770000000000000000 : ℝ)*(X 0 2+X 1 2)+(119280329387/71925000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8439/2048 : ℝ)) (lo := (71/625 : ℝ)) (hi := (14237/100000 : ℝ)) (c := (28760948569445436241/28770000000000000000 : ℝ)) (alpha := (119280329387/71925000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2117561777/10000000000 : ℝ)*X 0 0+(1078457661/2000000000 : ℝ)*X 0 1+(5266163169/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344582383/10000000000 : ℝ)*X 1 0+(-436305139/2000000000 : ℝ)*X 1 1+(2633081589/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344582409/10000000000 : ℝ)*X 2 0+(5266163183/10000000000 : ℝ)*X 2 1+(-545381413/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4350029161/10000000000 : ℝ)*X 0 0+(84476183/200000000 : ℝ)*X 0 1+(4479909731/10000000000 : ℝ)*X 0 2+(4350029161/10000000000 : ℝ)*X 1 0+(84476183/200000000 : ℝ)*X 1 1+(4479909731/10000000000 : ℝ)*X 1 2+(4350029161/10000000000 : ℝ)*X 2 0+(84476183/200000000 : ℝ)*X 2 1+(4479909731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-423513327/2000000000 : ℝ)*X 0 0+(210659487/400000000 : ℝ)*X 0 1+(269598157/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312390337/10000000000 : ℝ)*X 1 0+(-256965737/1250000000 : ℝ)*X 1 1+(1078392621/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1328097593/2500000000 : ℝ)*X 2 0+(5391963127/10000000000 : ℝ)*X 2 1+(-102786291/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((543754911/1250000000 : ℝ)*X 0 0+(4479251861/10000000000 : ℝ)*X 0 1+(4224469289/10000000000 : ℝ)*X 0 2+(543754911/1250000000 : ℝ)*X 1 0+(4479251861/10000000000 : ℝ)*X 1 1+(4224469289/10000000000 : ℝ)*X 1 2+(543754911/1250000000 : ℝ)*X 2 0+(4479251861/10000000000 : ℝ)*X 2 1+(4224469289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1247_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (489577534685691734142204747/47950000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (120803179/6250000000000 : ℝ)*(base19) + (378332349/20000000000000 : ℝ)*(base23) + (42628599/100000000000000 : ℝ)*(lower2) + (198224833/100000000000000 : ℝ)*(upper3) + (43006979/20000000000000 : ℝ)*(upper5) + (1183351466547333/20000000000000 : ℝ)*(major0) + (1183351466547333/20000000000000 : ℝ)*(major1) + (1183351466547333/20000000000000 : ℝ)*(major2) + (3964344176513813/50000000000000 : ℝ)*(sp0) + (3964371981601169/50000000000000 : ℝ)*(sp1) + (7928744004391457/100000000000000 : ℝ)*(sp2) + (15252898099803/390625000000 : ℝ)*(sp3) + (7192878197/12500000000000 : ℝ)*(sp4) + (26515531629/100000000000000 : ℝ)*(sp7) + (1952384214540599/50000000000000 : ℝ)*(f.failure) + (3964372948026601/50000000000000 : ℝ)*(f.sum) + (4888497561893/479500000000000000000000000 : ℝ)*base65 + (360746369384947393/27400000000000000000000000000000 : ℝ)*base67 + (529338489267347393/27400000000000000000000000000000 : ℝ)*base69 + (147830735977947393/27400000000000000000000000000000 : ℝ)*base71 + (6300812479047/959000000000000000000000000 : ℝ)*base73 + (177283802334652607/27400000000000000000000000000000 : ℝ)*base76 + (315166140201347393/27400000000000000000000000000000 : ℝ)*base77 + (485404699697547393/27400000000000000000000000000000 : ℝ)*base79 + (5831814328853/959000000000000000000000000 : ℝ)*base81 + (28208941/5000000000000000000000 : ℝ)*base89 + (28208941/5000000000000000000000 : ℝ)*base91 + (28208941/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1118765844900405675824759437/239750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (76037353/20000000000000 : ℝ)*(base19) + (695105453/100000000000000 : ℝ)*(base23) + (96194557/100000000000000 : ℝ)*(upper3) + (106450161/100000000000000 : ℝ)*(lower4) + (117550819/100000000000000 : ℝ)*(upper5) + (5947283607274243/100000000000000 : ℝ)*(major0) + (5947283607274243/100000000000000 : ℝ)*(major1) + (5947283607274243/100000000000000 : ℝ)*(major2) + (4062253691/100000000000000 : ℝ)*(sp1) + (3574671441/25000000000000 : ℝ)*(sp2) + (7969652792198087/100000000000000 : ℝ)*(sp4) + (7969648349757631/100000000000000 : ℝ)*(sp5) + (796963779840687/10000000000000 : ℝ)*(sp6) + (1962457133402109/50000000000000 : ℝ)*(sp7) + (1962457133402109/50000000000000 : ℝ)*(f.failure) + (7969652792198087/100000000000000 : ℝ)*(f.sum) + (26610466297649/14385000000000000000000000000 : ℝ)*base65 + (126951333866830503/137000000000000000000000000000000 : ℝ)*base67 + (2970853468383830503/137000000000000000000000000000000 : ℝ)*base69 + (1295209221809830503/137000000000000000000000000000000 : ℝ)*base71 + (44475277386481/14385000000000000000000000000 : ℝ)*base74 + (2340587561382830503/137000000000000000000000000000000 : ℝ)*base75 + (1047507219017830503/137000000000000000000000000000000 : ℝ)*base77 + (1626850751682169497/137000000000000000000000000000000 : ℝ)*base80 + (18176123108663/7192500000000000000000000000 : ℝ)*base82 + (49902031/5000000000000000000000 : ℝ)*base89 + (49902031/5000000000000000000000 : ℝ)*base91 + (49902031/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1247_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151526459/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14237/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (71/625 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (573/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3533/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1247_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1247_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151526459/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1621/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (119/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (573/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3533/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1247_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1247_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1247_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8439/2048 : ℝ) ≤ p) (hpb : p ≤ (1055/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151526459/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1621/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (119/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (573/5000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3533/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1247_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
