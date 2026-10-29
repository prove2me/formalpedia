-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1647_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:12:01.223851+00:00
-- url     : https://prove2.me/submissions/64306cda-96ed-4829-8a27-3de9bdee910d

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
theorem support_rectangle_w1647_s0_0 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-299587127/2000000000 : ℝ)*x 0 + (723628177/1250000000 : ℝ)*x 1 + (98390309/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (299587127/2000000000 : ℝ)^4907 ≤ (1815889677303/20000000000000 : ℝ)^3883 := by
    have hnat : (299587127 : ℕ)^4907*20000000000000^3883 ≤ 1815889677303^3883*2000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299587127 2000000000 1815889677303 20000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (723628177/1250000000 : ℝ)^4907 ≤ (5011887119009/10000000000000 : ℝ)^3883 := by
    have hnat : (723628177 : ℕ)^4907*10000000000000^3883 ≤ 5011887119009^3883*1250000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      723628177 1250000000 5011887119009 10000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (98390309/200000000 : ℝ)^4907 ≤ (40801680415173/100000000000000 : ℝ)^3883 := by
    have hnat : (98390309 : ℕ)^4907*100000000000000^3883 ≤ 40801680415173^3883*200000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98390309 200000000 40801680415173 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-299587127/2000000000 : ℝ), (723628177/1250000000 : ℝ), (98390309/200000000 : ℝ)] ![(1815889677303/20000000000000 : ℝ), (5011887119009/10000000000000 : ℝ), (40801680415173/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-299587127/2000000000 : ℝ)|^4907 ≤ (1815889677303/20000000000000 : ℝ)^3883
        have hw : |(-299587127/2000000000 : ℝ)|=(299587127/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(723628177/1250000000 : ℝ)|^4907 ≤ (5011887119009/10000000000000 : ℝ)^3883
        have hw : |(723628177/1250000000 : ℝ)|=(723628177/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(98390309/200000000 : ℝ)|^4907 ≤ (40801680415173/100000000000000 : ℝ)^3883
        have hw : |(98390309/200000000 : ℝ)|=(98390309/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s0_1 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2719363339/5000000000 : ℝ)*x 0 + (-987765877/5000000000 : ℝ)*x 1 + (196780651/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2719363339/5000000000 : ℝ)^4907 ≤ (46317408383311/100000000000000 : ℝ)^3883 := by
    have hnat : (2719363339 : ℕ)^4907*100000000000000^3883 ≤ 46317408383311^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719363339 5000000000 46317408383311 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (987765877/5000000000 : ℝ)^4907 ≤ (12880902538759/100000000000000 : ℝ)^3883 := by
    have hnat : (987765877 : ℕ)^4907*100000000000000^3883 ≤ 12880902538759^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987765877 5000000000 12880902538759 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (196780651/400000000 : ℝ)^4907 ≤ (2550105566377/6250000000000 : ℝ)^3883 := by
    have hnat : (196780651 : ℕ)^4907*6250000000000^3883 ≤ 2550105566377^3883*400000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196780651 400000000 2550105566377 6250000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2719363339/5000000000 : ℝ), (-987765877/5000000000 : ℝ), (196780651/400000000 : ℝ)] ![(46317408383311/100000000000000 : ℝ), (12880902538759/100000000000000 : ℝ), (2550105566377/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2719363339/5000000000 : ℝ)|^4907 ≤ (46317408383311/100000000000000 : ℝ)^3883
        have hw : |(2719363339/5000000000 : ℝ)|=(2719363339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-987765877/5000000000 : ℝ)|^4907 ≤ (12880902538759/100000000000000 : ℝ)^3883
        have hw : |(-987765877/5000000000 : ℝ)|=(987765877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(196780651/400000000 : ℝ)|^4907 ≤ (2550105566377/6250000000000 : ℝ)^3883
        have hw : |(196780651/400000000 : ℝ)|=(196780651/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s0_2 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1087745779/2000000000 : ℝ)*x 0 + (983902983/2000000000 : ℝ)*x 1 + (-1975530589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087745779/2000000000 : ℝ)^4907 ≤ (9263486448563/20000000000000 : ℝ)^3883 := by
    have hnat : (1087745779 : ℕ)^4907*20000000000000^3883 ≤ 9263486448563^3883*2000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087745779 2000000000 9263486448563 20000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (983902983/2000000000 : ℝ)^4907 ≤ (40801674807817/100000000000000 : ℝ)^3883 := by
    have hnat : (983902983 : ℕ)^4907*100000000000000^3883 ≤ 40801674807817^3883*2000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      983902983 2000000000 40801674807817 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1975530589/10000000000 : ℝ)^4907 ≤ (12880892939519/100000000000000 : ℝ)^3883 := by
    have hnat : (1975530589 : ℕ)^4907*100000000000000^3883 ≤ 12880892939519^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1975530589 10000000000 12880892939519 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087745779/2000000000 : ℝ), (983902983/2000000000 : ℝ), (-1975530589/10000000000 : ℝ)] ![(9263486448563/20000000000000 : ℝ), (40801674807817/100000000000000 : ℝ), (12880892939519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087745779/2000000000 : ℝ)|^4907 ≤ (9263486448563/20000000000000 : ℝ)^3883
        have hw : |(1087745779/2000000000 : ℝ)|=(1087745779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(983902983/2000000000 : ℝ)|^4907 ≤ (40801674807817/100000000000000 : ℝ)^3883
        have hw : |(983902983/2000000000 : ℝ)|=(983902983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1975530589/10000000000 : ℝ)|^4907 ≤ (12880892939519/100000000000000 : ℝ)^3883
        have hw : |(-1975530589/10000000000 : ℝ)|=(1975530589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s0_3 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (255751163/625000000 : ℝ)*x 0 + (3081876503/10000000000 : ℝ)*x 1 + (106460233/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (255751163/625000000 : ℝ)^4907 ≤ (4041199320583/12500000000000 : ℝ)^3883 := by
    have hnat : (255751163 : ℕ)^4907*12500000000000^3883 ≤ 4041199320583^3883*625000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      255751163 625000000 4041199320583 12500000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3081876503/10000000000 : ℝ)^4907 ≤ (5648704456907/25000000000000 : ℝ)^3883 := by
    have hnat : (3081876503 : ℕ)^4907*25000000000000^3883 ≤ 5648704456907^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3081876503 10000000000 5648704456907 25000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (106460233/200000000 : ℝ)^4907 ≤ (45075587591611/100000000000000 : ℝ)^3883 := by
    have hnat : (106460233 : ℕ)^4907*100000000000000^3883 ≤ 45075587591611^3883*200000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106460233 200000000 45075587591611 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(255751163/625000000 : ℝ), (3081876503/10000000000 : ℝ), (106460233/200000000 : ℝ)] ![(4041199320583/12500000000000 : ℝ), (5648704456907/25000000000000 : ℝ), (45075587591611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(255751163/625000000 : ℝ)|^4907 ≤ (4041199320583/12500000000000 : ℝ)^3883
        have hw : |(255751163/625000000 : ℝ)|=(255751163/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3081876503/10000000000 : ℝ)|^4907 ≤ (5648704456907/25000000000000 : ℝ)^3883
        have hw : |(3081876503/10000000000 : ℝ)|=(3081876503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(106460233/200000000 : ℝ)|^4907 ≤ (45075587591611/100000000000000 : ℝ)^3883
        have hw : |(106460233/200000000 : ℝ)|=(106460233/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s0_4 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-375066537/2500000000 : ℝ)*x 0 + (988223963/2000000000 : ℝ)*x 1 + (5766673373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (375066537/2500000000 : ℝ)^4907 ≤ (4548651604961/50000000000000 : ℝ)^3883 := by
    have hnat : (375066537 : ℕ)^4907*50000000000000^3883 ≤ 4548651604961^3883*2500000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      375066537 2500000000 4548651604961 50000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (988223963/2000000000 : ℝ)^4907 ≤ (41028247612691/100000000000000 : ℝ)^3883 := by
    have hnat : (988223963 : ℕ)^4907*100000000000000^3883 ≤ 41028247612691^3883*2000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      988223963 2000000000 41028247612691 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5766673373/10000000000 : ℝ)^4907 ≤ (24937224580521/50000000000000 : ℝ)^3883 := by
    have hnat : (5766673373 : ℕ)^4907*50000000000000^3883 ≤ 24937224580521^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5766673373 10000000000 24937224580521 50000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-375066537/2500000000 : ℝ), (988223963/2000000000 : ℝ), (5766673373/10000000000 : ℝ)] ![(4548651604961/50000000000000 : ℝ), (41028247612691/100000000000000 : ℝ), (24937224580521/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-375066537/2500000000 : ℝ)|^4907 ≤ (4548651604961/50000000000000 : ℝ)^3883
        have hw : |(-375066537/2500000000 : ℝ)|=(375066537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(988223963/2000000000 : ℝ)|^4907 ≤ (41028247612691/100000000000000 : ℝ)^3883
        have hw : |(988223963/2000000000 : ℝ)|=(988223963/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5766673373/10000000000 : ℝ)|^4907 ≤ (24937224580521/50000000000000 : ℝ)^3883
        have hw : |(5766673373/10000000000 : ℝ)|=(5766673373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s0_5 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1300358743/2500000000 : ℝ)*x 0 + (-1128372981/10000000000 : ℝ)*x 1 + (5766672943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1300358743/2500000000 : ℝ)^4907 ≤ (43778511055077/100000000000000 : ℝ)^3883 := by
    have hnat : (1300358743 : ℕ)^4907*100000000000000^3883 ≤ 43778511055077^3883*2500000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300358743 2500000000 43778511055077 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1128372981/10000000000 : ℝ)^4907 ≤ (79338055803/1250000000000 : ℝ)^3883 := by
    have hnat : (1128372981 : ℕ)^4907*1250000000000^3883 ≤ 79338055803^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128372981 10000000000 79338055803 1250000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5766672943/10000000000 : ℝ)^4907 ≤ (9974888892269/20000000000000 : ℝ)^3883 := by
    have hnat : (5766672943 : ℕ)^4907*20000000000000^3883 ≤ 9974888892269^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5766672943 10000000000 9974888892269 20000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1300358743/2500000000 : ℝ), (-1128372981/10000000000 : ℝ), (5766672943/10000000000 : ℝ)] ![(43778511055077/100000000000000 : ℝ), (79338055803/1250000000000 : ℝ), (9974888892269/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1300358743/2500000000 : ℝ)|^4907 ≤ (43778511055077/100000000000000 : ℝ)^3883
        have hw : |(1300358743/2500000000 : ℝ)|=(1300358743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1128372981/10000000000 : ℝ)|^4907 ≤ (79338055803/1250000000000 : ℝ)^3883
        have hw : |(-1128372981/10000000000 : ℝ)|=(1128372981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5766672943/10000000000 : ℝ)|^4907 ≤ (9974888892269/20000000000000 : ℝ)^3883
        have hw : |(5766672943/10000000000 : ℝ)|=(5766672943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s0_6 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2600717147/5000000000 : ℝ)*x 0 + (2883336853/5000000000 : ℝ)*x 1 + (-141046603/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2600717147/5000000000 : ℝ)^4907 ≤ (43778503843733/100000000000000 : ℝ)^3883 := by
    have hnat : (2600717147 : ℕ)^4907*100000000000000^3883 ≤ 43778503843733^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2600717147 5000000000 43778503843733 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2883336853/5000000000 : ℝ)^4907 ≤ (1994978112023/4000000000000 : ℝ)^3883 := by
    have hnat : (2883336853 : ℕ)^4907*4000000000000^3883 ≤ 1994978112023^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2883336853 5000000000 1994978112023 4000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (141046603/1250000000 : ℝ)^4907 ≤ (793380418529/12500000000000 : ℝ)^3883 := by
    have hnat : (141046603 : ℕ)^4907*12500000000000^3883 ≤ 793380418529^3883*1250000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141046603 1250000000 793380418529 12500000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2600717147/5000000000 : ℝ), (2883336853/5000000000 : ℝ), (-141046603/1250000000 : ℝ)] ![(43778503843733/100000000000000 : ℝ), (1994978112023/4000000000000 : ℝ), (793380418529/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2600717147/5000000000 : ℝ)|^4907 ≤ (43778503843733/100000000000000 : ℝ)^3883
        have hw : |(2600717147/5000000000 : ℝ)|=(2600717147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2883336853/5000000000 : ℝ)|^4907 ≤ (1994978112023/4000000000000 : ℝ)^3883
        have hw : |(2883336853/5000000000 : ℝ)|=(2883336853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-141046603/1250000000 : ℝ)|^4907 ≤ (793380418529/12500000000000 : ℝ)^3883
        have hw : |(-141046603/1250000000 : ℝ)|=(141046603/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s0_7 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (512253753/1250000000 : ℝ)*x 0 + (2633663947/5000000000 : ℝ)*x 1 + (3139482879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (512253753/1250000000 : ℝ)^4907 ≤ (8097406274279/25000000000000 : ℝ)^3883 := by
    have hnat : (512253753 : ℕ)^4907*25000000000000^3883 ≤ 8097406274279^3883*1250000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512253753 1250000000 8097406274279 25000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633663947/5000000000 : ℝ)^4907 ≤ (11120132100789/25000000000000 : ℝ)^3883 := by
    have hnat : (2633663947 : ℕ)^4907*25000000000000^3883 ≤ 11120132100789^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633663947 5000000000 11120132100789 25000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3139482879/10000000000 : ℝ)^4907 ≤ (23129846490667/100000000000000 : ℝ)^3883 := by
    have hnat : (3139482879 : ℕ)^4907*100000000000000^3883 ≤ 23129846490667^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3139482879 10000000000 23129846490667 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(512253753/1250000000 : ℝ), (2633663947/5000000000 : ℝ), (3139482879/10000000000 : ℝ)] ![(8097406274279/25000000000000 : ℝ), (11120132100789/25000000000000 : ℝ), (23129846490667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(512253753/1250000000 : ℝ)|^4907 ≤ (8097406274279/25000000000000 : ℝ)^3883
        have hw : |(512253753/1250000000 : ℝ)|=(512253753/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633663947/5000000000 : ℝ)|^4907 ≤ (11120132100789/25000000000000 : ℝ)^3883
        have hw : |(2633663947/5000000000 : ℝ)|=(2633663947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3139482879/10000000000 : ℝ)|^4907 ≤ (23129846490667/100000000000000 : ℝ)^3883
        have hw : |(3139482879/10000000000 : ℝ)|=(3139482879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1647_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89436883/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (2393/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (23421/100000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (4903/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4903 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4903*1^1024 ≤ 0^1024*1^4903 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4903 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4903/1024 : ℝ) ≤ (248690408765673959/20000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4903 ≤ (248690408765673959/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4903*20000000000000000000^1024 ≤ 248690408765673959^1024*5^4903 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 248690408765673959 20000000000000000000 4903 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (248690408765673959/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4903/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4903 := by
      have hnat : (1 : ℕ)^1024*1^4903 ≤ 1^4903*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20248690408765673959/20000000000000000000 : ℝ) ≤ (1253230363908649/1250000000000000 : ℝ) ^ (4903/1024 : ℝ) := by
    have hpowers : (20248690408765673959/20000000000000000000 : ℝ)^1024 ≤ (1253230363908649/1250000000000000 : ℝ)^4903 := by
      have hnat : (20248690408765673959 : ℕ)^1024*1250000000000000^4903 ≤ 1253230363908649^4903*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20248690408765673959 20000000000000000000 1253230363908649 1250000000000000 1024 4903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1253230363908649/1250000000000000 : ℝ)) (X := (20248690408765673959/20000000000000000000 : ℝ)) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10248690408765673959/10000000000000000000 : ℝ) ≤ (628230363908649/625000000000000 : ℝ) ^ (4903/1024 : ℝ) := by
    have hpowers : (10248690408765673959/10000000000000000000 : ℝ)^1024 ≤ (628230363908649/625000000000000 : ℝ)^4903 := by
      have hnat : (10248690408765673959 : ℕ)^1024*625000000000000^4903 ≤ 628230363908649^4903*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10248690408765673959 10000000000000000000 628230363908649 625000000000000 1024 4903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (628230363908649/625000000000000 : ℝ)) (X := (10248690408765673959/10000000000000000000 : ℝ)) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(3230363908649/500000000000000 : ℝ)*(0 : ℝ))^(4903/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(3230363908649/500000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(248690408765673959/20000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(3230363908649/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4903/1024 : ℝ) := by
    rw [show (1 : ℝ)+(3230363908649/500000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1253230363908649/1250000000000000 : ℝ) by norm_num, show 1+(248690408765673959/20000000000000000000 : ℝ)+(0 : ℝ)=(20248690408765673959/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(248690408765673959/20000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(3230363908649/500000000000000 : ℝ)*(2/5 : ℝ))^(4903/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(3230363908649/500000000000000 : ℝ)*(2/5 : ℝ)=(628230363908649/625000000000000 : ℝ) by norm_num, show 1+2*(248690408765673959/20000000000000000000 : ℝ)=(10248690408765673959/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(3230363908649/500000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4903/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3230363908649/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(3230363908649/500000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4903/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3230363908649/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(3230363908649/500000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4903/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (3230363908649/500000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-299587127/2000000000 : ℝ)*X 0 0+(723628177/1250000000 : ℝ)*X 0 1+(98390309/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2719363339/5000000000 : ℝ)*X 1 0+(-987765877/5000000000 : ℝ)*X 1 1+(196780651/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1087745779/2000000000 : ℝ)*X 2 0+(983902983/2000000000 : ℝ)*X 2 1+(-1975530589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((255751163/625000000 : ℝ)*X 0 0+(3081876503/10000000000 : ℝ)*X 0 1+(106460233/200000000 : ℝ)*X 0 2+(255751163/625000000 : ℝ)*X 1 0+(3081876503/10000000000 : ℝ)*X 1 1+(106460233/200000000 : ℝ)*X 1 2+(255751163/625000000 : ℝ)*X 2 0+(3081876503/10000000000 : ℝ)*X 2 1+(106460233/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-375066537/2500000000 : ℝ)*X 0 0+(988223963/2000000000 : ℝ)*X 0 1+(5766673373/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1300358743/2500000000 : ℝ)*X 1 0+(-1128372981/10000000000 : ℝ)*X 1 1+(5766672943/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2600717147/5000000000 : ℝ)*X 2 0+(2883336853/5000000000 : ℝ)*X 2 1+(-141046603/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((512253753/1250000000 : ℝ)*X 0 0+(2633663947/5000000000 : ℝ)*X 0 1+(3139482879/10000000000 : ℝ)*X 0 2+(512253753/1250000000 : ℝ)*X 1 0+(2633663947/5000000000 : ℝ)*X 1 1+(3139482879/10000000000 : ℝ)*X 1 2+(512253753/1250000000 : ℝ)*X 2 0+(2633663947/5000000000 : ℝ)*X 2 1+(3139482879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5568817619618272273737/1562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (35504733/20000000000000 : ℝ)*(base19) + (255014731/100000000000000 : ℝ)*(base23) + (56986291/100000000000000 : ℝ)*(base24) + (18195811/10000000000000 : ℝ)*(upper4) + (50630761/100000000000000 : ℝ)*(upper5) + (199534678168411/25000000000000 : ℝ)*(major0) + (199534678168411/25000000000000 : ℝ)*(major1) + (199534678168411/25000000000000 : ℝ)*(major2) + (287518224473297/25000000000000 : ℝ)*(sp0) + (575037452494697/50000000000000 : ℝ)*(sp1) + (143759346972957/12500000000000 : ℝ)*(sp2) + (446202218761159/100000000000000 : ℝ)*(sp3) + (2189891489/100000000000000 : ℝ)*(sp4) + (2635809/50000000000000 : ℝ)*(sp5) + (446202218761159/100000000000000 : ℝ)*(f.failure) + (575037543892339/50000000000000 : ℝ)*(f.sum) + (16779504486739/6250000000000000000000000000 : ℝ)*base65 + (142519144986739/12500000000000000000000000000 : ℝ)*base67 + (76997749649239/12500000000000000000000000000 : ℝ)*base69 + (128262185236739/12500000000000000000000000000 : ℝ)*base71 + (6611387467989/6250000000000000000000000000 : ℝ)*base73 + (87242223061739/12500000000000000000000000000 : ℝ)*base75 + (59801406586739/12500000000000000000000000000 : ℝ)*base77 + (25991538774239/12500000000000000000000000000 : ℝ)*base79 + (9382185449239/6250000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (17572603/5000000000000000000000 : ℝ)*base90 + (17572603/5000000000000000000000 : ℝ)*base92 + (17572603/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (200593382936927642355639/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1737398519/100000000000000 : ℝ)*(base19) + (1609595291/100000000000000 : ℝ)*(base23) + (110637621/100000000000000 : ℝ)*(base32) + (308594107/100000000000000 : ℝ)*(upper3) + (193890303/100000000000000 : ℝ)*(upper5) + (840633234145163/100000000000000 : ℝ)*(major0) + (840633234145163/100000000000000 : ℝ)*(major1) + (840633234145163/100000000000000 : ℝ)*(major2) + (276525959/6250000000000 : ℝ)*(sp1) + (158871889/3125000000000 : ℝ)*(sp2) + (605653636142767/50000000000000 : ℝ)*(sp4) + (151412638808959/12500000000000 : ℝ)*(sp5) + (302825144697449/25000000000000 : ℝ)*(sp6) + (11748970447733/2500000000000 : ℝ)*(sp7) + (469958928546941/100000000000000 : ℝ)*(f.failure) + (605653636142767/50000000000000 : ℝ)*(f.sum) + (6721078985213/25000000000000000000000000000 : ℝ)*base66 + (299565522714787/50000000000000000000000000000 : ℝ)*base67 + (94486014114787/50000000000000000000000000000 : ℝ)*base69 + (787267585213/50000000000000000000000000000 : ℝ)*base72 + (113980825414787/25000000000000000000000000000 : ℝ)*base73 + (269874391585213/50000000000000000000000000000 : ℝ)*base76 + (183349695985213/50000000000000000000000000000 : ℝ)*base78 + (8554038414787/50000000000000000000000000000 : ℝ)*base79 + (27636324614787/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (27775097/5000000000000000000000 : ℝ)*base90 + (27775097/5000000000000000000000 : ℝ)*base92 + (27775097/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1647_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89436883/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2393/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (23421/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1647_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1647_s1_0 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1605056461/10000000000 : ℝ)*x 0 + (1099708893/2000000000 : ℝ)*x 1 + (5140398691/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1605056461/10000000000 : ℝ)^4907 ≤ (9907573115827/100000000000000 : ℝ)^3883 := by
    have hnat : (1605056461 : ℕ)^4907*100000000000000^3883 ≤ 9907573115827^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1605056461 10000000000 9907573115827 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1099708893/2000000000 : ℝ)^4907 ≤ (11740525624581/25000000000000 : ℝ)^3883 := by
    have hnat : (1099708893 : ℕ)^4907*25000000000000^3883 ≤ 11740525624581^3883*2000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099708893 2000000000 11740525624581 25000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5140398691/10000000000 : ℝ)^4907 ≤ (43130324373747/100000000000000 : ℝ)^3883 := by
    have hnat : (5140398691 : ℕ)^4907*100000000000000^3883 ≤ 43130324373747^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140398691 10000000000 43130324373747 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1605056461/10000000000 : ℝ), (1099708893/2000000000 : ℝ), (5140398691/10000000000 : ℝ)] ![(9907573115827/100000000000000 : ℝ), (11740525624581/25000000000000 : ℝ), (43130324373747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1605056461/10000000000 : ℝ)|^4907 ≤ (9907573115827/100000000000000 : ℝ)^3883
        have hw : |(-1605056461/10000000000 : ℝ)|=(1605056461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1099708893/2000000000 : ℝ)|^4907 ≤ (11740525624581/25000000000000 : ℝ)^3883
        have hw : |(1099708893/2000000000 : ℝ)|=(1099708893/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5140398691/10000000000 : ℝ)|^4907 ≤ (43130324373747/100000000000000 : ℝ)^3883
        have hw : |(5140398691/10000000000 : ℝ)|=(5140398691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s1_1 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5361465653/10000000000 : ℝ)*x 0 + (-1791324011/10000000000 : ℝ)*x 1 + (5140398529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5361465653/10000000000 : ℝ)^4907 ≤ (45487483010903/100000000000000 : ℝ)^3883 := by
    have hnat : (5361465653 : ℕ)^4907*100000000000000^3883 ≤ 45487483010903^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5361465653 10000000000 45487483010903 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1791324011/10000000000 : ℝ)^4907 ≤ (5691097156993/50000000000000 : ℝ)^3883 := by
    have hnat : (1791324011 : ℕ)^4907*50000000000000^3883 ≤ 5691097156993^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1791324011 10000000000 5691097156993 50000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5140398529/10000000000 : ℝ)^4907 ≤ (21565161328019/50000000000000 : ℝ)^3883 := by
    have hnat : (5140398529 : ℕ)^4907*50000000000000^3883 ≤ 21565161328019^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140398529 10000000000 21565161328019 50000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5361465653/10000000000 : ℝ), (-1791324011/10000000000 : ℝ), (5140398529/10000000000 : ℝ)] ![(45487483010903/100000000000000 : ℝ), (5691097156993/50000000000000 : ℝ), (21565161328019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5361465653/10000000000 : ℝ)|^4907 ≤ (45487483010903/100000000000000 : ℝ)^3883
        have hw : |(5361465653/10000000000 : ℝ)|=(5361465653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1791324011/10000000000 : ℝ)|^4907 ≤ (5691097156993/50000000000000 : ℝ)^3883
        have hw : |(-1791324011/10000000000 : ℝ)|=(1791324011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5140398529/10000000000 : ℝ)|^4907 ≤ (21565161328019/50000000000000 : ℝ)^3883
        have hw : |(5140398529/10000000000 : ℝ)|=(5140398529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s1_2 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2680733389/5000000000 : ℝ)*x 0 + (205615891/400000000 : ℝ)*x 1 + (-447831041/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2680733389/5000000000 : ℝ)^4907 ≤ (45487495072633/100000000000000 : ℝ)^3883 := by
    have hnat : (2680733389 : ℕ)^4907*100000000000000^3883 ≤ 45487495072633^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2680733389 5000000000 45487495072633 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (205615891/400000000 : ℝ)^4907 ≤ (43130309359699/100000000000000 : ℝ)^3883 := by
    have hnat : (205615891 : ℕ)^4907*100000000000000^3883 ≤ 43130309359699^3883*400000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205615891 400000000 43130309359699 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (447831041/2500000000 : ℝ)^4907 ≤ (11382195542533/100000000000000 : ℝ)^3883 := by
    have hnat : (447831041 : ℕ)^4907*100000000000000^3883 ≤ 11382195542533^3883*2500000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447831041 2500000000 11382195542533 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2680733389/5000000000 : ℝ), (205615891/400000000 : ℝ), (-447831041/2500000000 : ℝ)] ![(45487495072633/100000000000000 : ℝ), (43130309359699/100000000000000 : ℝ), (11382195542533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2680733389/5000000000 : ℝ)|^4907 ≤ (45487495072633/100000000000000 : ℝ)^3883
        have hw : |(2680733389/5000000000 : ℝ)|=(2680733389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(205615891/400000000 : ℝ)|^4907 ≤ (43130309359699/100000000000000 : ℝ)^3883
        have hw : |(205615891/400000000 : ℝ)|=(205615891/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-447831041/2500000000 : ℝ)|^4907 ≤ (11382195542533/100000000000000 : ℝ)^3883
        have hw : |(-447831041/2500000000 : ℝ)|=(447831041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s1_3 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2087697841/5000000000 : ℝ)*x 0 + (466547347/1250000000 : ℝ)*x 1 + (931098479/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2087697841/5000000000 : ℝ)^4907 ≤ (33164269633503/100000000000000 : ℝ)^3883 := by
    have hnat : (2087697841 : ℕ)^4907*100000000000000^3883 ≤ 33164269633503^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087697841 5000000000 33164269633503 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (466547347/1250000000 : ℝ)^4907 ≤ (1151257582197/4000000000000 : ℝ)^3883 := by
    have hnat : (466547347 : ℕ)^4907*4000000000000^3883 ≤ 1151257582197^3883*1250000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466547347 1250000000 1151257582197 4000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (931098479/2000000000 : ℝ)^4907 ≤ (9513572697059/25000000000000 : ℝ)^3883 := by
    have hnat : (931098479 : ℕ)^4907*25000000000000^3883 ≤ 9513572697059^3883*2000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931098479 2000000000 9513572697059 25000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2087697841/5000000000 : ℝ), (466547347/1250000000 : ℝ), (931098479/2000000000 : ℝ)] ![(33164269633503/100000000000000 : ℝ), (1151257582197/4000000000000 : ℝ), (9513572697059/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2087697841/5000000000 : ℝ)|^4907 ≤ (33164269633503/100000000000000 : ℝ)^3883
        have hw : |(2087697841/5000000000 : ℝ)|=(2087697841/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(466547347/1250000000 : ℝ)|^4907 ≤ (1151257582197/4000000000000 : ℝ)^3883
        have hw : |(466547347/1250000000 : ℝ)|=(466547347/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(931098479/2000000000 : ℝ)|^4907 ≤ (9513572697059/25000000000000 : ℝ)^3883
        have hw : |(931098479/2000000000 : ℝ)|=(931098479/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s1_4 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1605217517/10000000000 : ℝ)*x 0 + (5144049593/10000000000 : ℝ)*x 1 + (549484077/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1605217517/10000000000 : ℝ)^4907 ≤ (2477207364757/25000000000000 : ℝ)^3883 := by
    have hnat : (1605217517 : ℕ)^4907*25000000000000^3883 ≤ 2477207364757^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1605217517 10000000000 2477207364757 25000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5144049593/10000000000 : ℝ)^4907 ≤ (43169039031603/100000000000000 : ℝ)^3883 := by
    have hnat : (5144049593 : ℕ)^4907*100000000000000^3883 ≤ 43169039031603^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5144049593 10000000000 43169039031603 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (549484077/1000000000 : ℝ)^4907 ≤ (46922131491013/100000000000000 : ℝ)^3883 := by
    have hnat : (549484077 : ℕ)^4907*100000000000000^3883 ≤ 46922131491013^3883*1000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549484077 1000000000 46922131491013 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1605217517/10000000000 : ℝ), (5144049593/10000000000 : ℝ), (549484077/1000000000 : ℝ)] ![(2477207364757/25000000000000 : ℝ), (43169039031603/100000000000000 : ℝ), (46922131491013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1605217517/10000000000 : ℝ)|^4907 ≤ (2477207364757/25000000000000 : ℝ)^3883
        have hw : |(-1605217517/10000000000 : ℝ)|=(1605217517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5144049593/10000000000 : ℝ)|^4907 ≤ (43169039031603/100000000000000 : ℝ)^3883
        have hw : |(5144049593/10000000000 : ℝ)|=(5144049593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(549484077/1000000000 : ℝ)|^4907 ≤ (46922131491013/100000000000000 : ℝ)^3883
        have hw : |(549484077/1000000000 : ℝ)|=(549484077/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s1_5 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (263286809/500000000 : ℝ)*x 0 + (-22451269/156250000 : ℝ)*x 1 + (2747420391/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263286809/500000000 : ℝ)^4907 ≤ (44463542995253/100000000000000 : ℝ)^3883 := by
    have hnat : (263286809 : ℕ)^4907*100000000000000^3883 ≤ 44463542995253^3883*500000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263286809 500000000 44463542995253 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (22451269/156250000 : ℝ)^4907 ≤ (4307162683689/50000000000000 : ℝ)^3883 := by
    have hnat : (22451269 : ℕ)^4907*50000000000000^3883 ≤ 4307162683689^3883*156250000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22451269 156250000 4307162683689 50000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2747420391/5000000000 : ℝ)^4907 ≤ (11730532905127/25000000000000 : ℝ)^3883 := by
    have hnat : (2747420391 : ℕ)^4907*25000000000000^3883 ≤ 11730532905127^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747420391 5000000000 11730532905127 25000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263286809/500000000 : ℝ), (-22451269/156250000 : ℝ), (2747420391/5000000000 : ℝ)] ![(44463542995253/100000000000000 : ℝ), (4307162683689/50000000000000 : ℝ), (11730532905127/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263286809/500000000 : ℝ)|^4907 ≤ (44463542995253/100000000000000 : ℝ)^3883
        have hw : |(263286809/500000000 : ℝ)|=(263286809/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-22451269/156250000 : ℝ)|^4907 ≤ (4307162683689/50000000000000 : ℝ)^3883
        have hw : |(-22451269/156250000 : ℝ)|=(22451269/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2747420391/5000000000 : ℝ)|^4907 ≤ (11730532905127/25000000000000 : ℝ)^3883
        have hw : |(2747420391/5000000000 : ℝ)|=(2747420391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s1_6 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5265735999/10000000000 : ℝ)*x 0 + (1373710261/2500000000 : ℝ)*x 1 + (-1436881099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5265735999/10000000000 : ℝ)^4907 ≤ (44463541063853/100000000000000 : ℝ)^3883 := by
    have hnat : (5265735999 : ℕ)^4907*100000000000000^3883 ≤ 44463541063853^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265735999 10000000000 44463541063853 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1373710261/2500000000 : ℝ)^4907 ≤ (11730533611953/25000000000000 : ℝ)^3883 := by
    have hnat : (1373710261 : ℕ)^4907*25000000000000^3883 ≤ 11730533611953^3883*2500000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1373710261 2500000000 11730533611953 25000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1436881099/10000000000 : ℝ)^4907 ≤ (1076790560121/12500000000000 : ℝ)^3883 := by
    have hnat : (1436881099 : ℕ)^4907*12500000000000^3883 ≤ 1076790560121^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1436881099 10000000000 1076790560121 12500000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5265735999/10000000000 : ℝ), (1373710261/2500000000 : ℝ), (-1436881099/10000000000 : ℝ)] ![(44463541063853/100000000000000 : ℝ), (11730533611953/25000000000000 : ℝ), (1076790560121/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5265735999/10000000000 : ℝ)|^4907 ≤ (44463541063853/100000000000000 : ℝ)^3883
        have hw : |(5265735999/10000000000 : ℝ)|=(5265735999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1373710261/2500000000 : ℝ)|^4907 ≤ (11730533611953/25000000000000 : ℝ)^3883
        have hw : |(1373710261/2500000000 : ℝ)|=(1373710261/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1436881099/10000000000 : ℝ)|^4907 ≤ (1076790560121/12500000000000 : ℝ)^3883
        have hw : |(-1436881099/10000000000 : ℝ)|=(1436881099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s1_7 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2087903519/5000000000 : ℝ)*x 0 + (4646081001/10000000000 : ℝ)*x 1 + (935481347/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2087903519/5000000000 : ℝ)^4907 ≤ (8292099658523/25000000000000 : ℝ)^3883 := by
    have hnat : (2087903519 : ℕ)^4907*25000000000000^3883 ≤ 8292099658523^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087903519 5000000000 8292099658523 25000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4646081001/10000000000 : ℝ)^4907 ≤ (9489275017243/25000000000000 : ℝ)^3883 := by
    have hnat : (4646081001 : ℕ)^4907*25000000000000^3883 ≤ 9489275017243^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4646081001 10000000000 9489275017243 25000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (935481347/2500000000 : ℝ)^4907 ≤ (28874501279099/100000000000000 : ℝ)^3883 := by
    have hnat : (935481347 : ℕ)^4907*100000000000000^3883 ≤ 28874501279099^3883*2500000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      935481347 2500000000 28874501279099 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2087903519/5000000000 : ℝ), (4646081001/10000000000 : ℝ), (935481347/2500000000 : ℝ)] ![(8292099658523/25000000000000 : ℝ), (9489275017243/25000000000000 : ℝ), (28874501279099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2087903519/5000000000 : ℝ)|^4907 ≤ (8292099658523/25000000000000 : ℝ)^3883
        have hw : |(2087903519/5000000000 : ℝ)|=(2087903519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4646081001/10000000000 : ℝ)|^4907 ≤ (9489275017243/25000000000000 : ℝ)^3883
        have hw : |(4646081001/10000000000 : ℝ)|=(4646081001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(935481347/2500000000 : ℝ)|^4907 ≤ (28874501279099/100000000000000 : ℝ)^3883
        have hw : |(935481347/2500000000 : ℝ)|=(935481347/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1647_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89436883/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23421/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2393/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2429/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4331/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (23421/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2393/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (23421/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2393/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (23421/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2393/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (23421/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2393/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (23421/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2393/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (23421/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2393/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2393/50000 : ℝ) ^ (4903/1024 : ℝ) ≤ (23909242929843/50000000000000000000 : ℝ) := by
    have hpowers : (2393/50000 : ℝ)^4903 ≤ (23909242929843/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2393 : ℕ)^4903*50000000000000000000^1024 ≤ 23909242929843^1024*50000^4903 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2393 50000 23909242929843 50000000000000000000 4903 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2393/50000 : ℝ)) (X := (23909242929843/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (23421/100000 : ℝ) ^ (4903/1024 : ℝ) ≤ (95855413252452489/100000000000000000000 : ℝ) := by
    have hpowers : (23421/100000 : ℝ)^4903 ≤ (95855413252452489/100000000000000000000 : ℝ)^1024 := by
      have hnat : (23421 : ℕ)^4903*100000000000000000000^1024 ≤ 95855413252452489^1024*100000^4903 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23421 100000 95855413252452489 100000000000000000000 4903 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23421/100000 : ℝ)) (X := (95855413252452489/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000023909242929843/25000000000000000000 : ℝ) ≤ (5000000998696941/5000000000000000 : ℝ) ^ (4903/1024 : ℝ) := by
    have hpowers : (25000023909242929843/25000000000000000000 : ℝ)^1024 ≤ (5000000998696941/5000000000000000 : ℝ)^4903 := by
      have hnat : (25000023909242929843 : ℕ)^1024*5000000000000000^4903 ≤ 5000000998696941^4903*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000023909242929843 25000000000000000000 5000000998696941 5000000000000000 1024 4903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000998696941/5000000000000000 : ℝ)) (X := (25000023909242929843/25000000000000000000 : ℝ)) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4003836129269532487/4000000000000000000 : ℝ) ≤ (10002002196099949/10000000000000000 : ℝ) ^ (4903/1024 : ℝ) := by
    have hpowers : (4003836129269532487/4000000000000000000 : ℝ)^1024 ≤ (10002002196099949/10000000000000000 : ℝ)^4903 := by
      have hnat : (4003836129269532487 : ℕ)^1024*10000000000000000^4903 ≤ 10002002196099949^4903*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4003836129269532487 4000000000000000000 10002002196099949 10000000000000000 1024 4903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002002196099949/10000000000000000 : ℝ)) (X := (4003836129269532487/4000000000000000000 : ℝ)) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50095855413252452489/50000000000000000000 : ℝ) ≤ (39078134354711/39062500000000 : ℝ) ^ (4903/1024 : ℝ) := by
    have hpowers : (50095855413252452489/50000000000000000000 : ℝ)^1024 ≤ (39078134354711/39062500000000 : ℝ)^4903 := by
      have hnat : (50095855413252452489 : ℕ)^1024*39062500000000^4903 ≤ 39078134354711^4903*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50095855413252452489 50000000000000000000 39078134354711 39062500000000 1024 4903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (39078134354711/39062500000000 : ℝ)) (X := (50095855413252452489/50000000000000000000 : ℝ)) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(23909242929843/50000000000000000000 : ℝ) ≤ ((93165445659710258873/93175000000000000000 : ℝ)+2*(2000198706067/1863500000000000 : ℝ)*(2393/50000 : ℝ))^(4903/1024 : ℝ) := by
    rw [show (93165445659710258873/93175000000000000000 : ℝ)+2*(2000198706067/1863500000000000 : ℝ)*(2393/50000 : ℝ)=(5000000998696941/5000000000000000 : ℝ) by norm_num, show 1+2*(23909242929843/50000000000000000000 : ℝ)=(25000023909242929843/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(95855413252452489/100000000000000000000 : ℝ)+(23909242929843/50000000000000000000 : ℝ) ≤ ((93165445659710258873/93175000000000000000 : ℝ)+(2000198706067/1863500000000000 : ℝ)*((23421/100000 : ℝ)+(2393/50000 : ℝ)))^(4903/1024 : ℝ) := by
    rw [show (93165445659710258873/93175000000000000000 : ℝ)+(2000198706067/1863500000000000 : ℝ)*((23421/100000 : ℝ)+(2393/50000 : ℝ))=(10002002196099949/10000000000000000 : ℝ) by norm_num, show 1+(95855413252452489/100000000000000000000 : ℝ)+(23909242929843/50000000000000000000 : ℝ)=(4003836129269532487/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(95855413252452489/100000000000000000000 : ℝ) ≤ ((93165445659710258873/93175000000000000000 : ℝ)+2*(2000198706067/1863500000000000 : ℝ)*(23421/100000 : ℝ))^(4903/1024 : ℝ) := by
    rw [show (93165445659710258873/93175000000000000000 : ℝ)+2*(2000198706067/1863500000000000 : ℝ)*(23421/100000 : ℝ)=(39078134354711/39062500000000 : ℝ) by norm_num, show 1+2*(95855413252452489/100000000000000000000 : ℝ)=(50095855413252452489/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (93165445659710258873/93175000000000000000 : ℝ)*(X 1 0+X 2 0)+(2000198706067/1863500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4903/1024 : ℝ)) (lo := (2393/50000 : ℝ)) (hi := (23421/100000 : ℝ)) (c := (93165445659710258873/93175000000000000000 : ℝ)) (alpha := (2000198706067/1863500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (93165445659710258873/93175000000000000000 : ℝ)*(X 0 1+X 2 1)+(2000198706067/1863500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4903/1024 : ℝ)) (lo := (2393/50000 : ℝ)) (hi := (23421/100000 : ℝ)) (c := (93165445659710258873/93175000000000000000 : ℝ)) (alpha := (2000198706067/1863500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (93165445659710258873/93175000000000000000 : ℝ)*(X 0 2+X 1 2)+(2000198706067/1863500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4903/1024 : ℝ)) (lo := (2393/50000 : ℝ)) (hi := (23421/100000 : ℝ)) (c := (93165445659710258873/93175000000000000000 : ℝ)) (alpha := (2000198706067/1863500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1605056461/10000000000 : ℝ)*X 0 0+(1099708893/2000000000 : ℝ)*X 0 1+(5140398691/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5361465653/10000000000 : ℝ)*X 1 0+(-1791324011/10000000000 : ℝ)*X 1 1+(5140398529/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2680733389/5000000000 : ℝ)*X 2 0+(205615891/400000000 : ℝ)*X 2 1+(-447831041/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2087697841/5000000000 : ℝ)*X 0 0+(466547347/1250000000 : ℝ)*X 0 1+(931098479/2000000000 : ℝ)*X 0 2+(2087697841/5000000000 : ℝ)*X 1 0+(466547347/1250000000 : ℝ)*X 1 1+(931098479/2000000000 : ℝ)*X 1 2+(2087697841/5000000000 : ℝ)*X 2 0+(466547347/1250000000 : ℝ)*X 2 1+(931098479/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1605217517/10000000000 : ℝ)*X 0 0+(5144049593/10000000000 : ℝ)*X 0 1+(549484077/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((263286809/500000000 : ℝ)*X 1 0+(-22451269/156250000 : ℝ)*X 1 1+(2747420391/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5265735999/10000000000 : ℝ)*X 2 0+(1373710261/2500000000 : ℝ)*X 2 1+(-1436881099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2087903519/5000000000 : ℝ)*X 0 0+(4646081001/10000000000 : ℝ)*X 0 1+(935481347/2500000000 : ℝ)*X 0 2+(2087903519/5000000000 : ℝ)*X 1 0+(4646081001/10000000000 : ℝ)*X 1 1+(935481347/2500000000 : ℝ)*X 1 2+(2087903519/5000000000 : ℝ)*X 2 0+(4646081001/10000000000 : ℝ)*X 2 1+(935481347/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (49047683003403169751729394783/4658750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (701762531/100000000000000 : ℝ)*(base1) + (517258361/50000000000000 : ℝ)*(base19) + (12963173/800000000000 : ℝ)*(base23) + (1786149/2000000000000 : ℝ)*(upper3) + (42569651/50000000000000 : ℝ)*(upper5) + (1937724580477443/100000000000000 : ℝ)*(major0) + (1937724580477443/100000000000000 : ℝ)*(major1) + (1937724580477443/100000000000000 : ℝ)*(major2) + (1396078823044747/50000000000000 : ℝ)*(sp0) + (27921561202701/1000000000000 : ℝ)*(sp1) + (1396077767195099/50000000000000 : ℝ)*(sp2) + (54164512197873/5000000000000 : ℝ)*(sp3) + (10522993/5000000000000 : ℝ)*(sp4) + (88689017/12500000000000 : ℝ)*(sp7) + (8463216056501/781250000000 : ℝ)*(f.failure) + (2792157154786823/100000000000000 : ℝ)*(f.sum) + (78480407891231/93175000000000000000000000000 : ℝ)*base65 + (20414504537246151739/9317500000000000000000000000000000 : ℝ)*base67 + (26696501399183848261/9317500000000000000000000000000000 : ℝ)*base70 + (32478883649111151739/9317500000000000000000000000000000 : ℝ)*base71 + (212707058569381/93175000000000000000000000000 : ℝ)*base73 + (31819836561961151739/9317500000000000000000000000000000 : ℝ)*base75 + (12552283988108848261/9317500000000000000000000000000000 : ℝ)*base78 + (27107052720946151739/9317500000000000000000000000000000 : ℝ)*base79 + (46305931055619/93175000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (38627/9765625000000000000 : ℝ)*base89 + (38627/9765625000000000000 : ℝ)*base91 + (38627/9765625000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30369401442648099650057150259/4658750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (255674371/20000000000000 : ℝ)*(base19) + (1249348173/100000000000000 : ℝ)*(base23) + (24562693/100000000000000 : ℝ)*(upper2) + (8158903/5000000000000 : ℝ)*(upper3) + (5018907/3125000000000 : ℝ)*(upper5) + (1978351319293561/100000000000000 : ℝ)*(major0) + (1978351319293561/100000000000000 : ℝ)*(major1) + (1978351319293561/100000000000000 : ℝ)*(major2) + (11741536141/100000000000000 : ℝ)*(sp1) + (3242241569/25000000000000 : ℝ)*(sp2) + (1425349123327721/50000000000000 : ℝ)*(sp4) + (1425342613373723/50000000000000 : ℝ)*(sp5) + (2850684028340993/100000000000000 : ℝ)*(sp6) + (1106004174638757/100000000000000 : ℝ)*(sp7) + (1106004174638757/100000000000000 : ℝ)*(f.failure) + (1425349123327721/50000000000000 : ℝ)*(f.sum) + (264394559695513/93175000000000000000000000000 : ℝ)*base66 + (109260842422481133247/9317500000000000000000000000000000 : ℝ)*base68 + (27569978944241366753/9317500000000000000000000000000000 : ℝ)*base69 + (4687206642761133247/9317500000000000000000000000000000 : ℝ)*base72 + (560561138152663/93175000000000000000000000000 : ℝ)*base74 + (8488586641073866753/9317500000000000000000000000000000 : ℝ)*base75 + (35522768322046133247/9317500000000000000000000000000000 : ℝ)*base78 + (130225958033286133247/9317500000000000000000000000000000 : ℝ)*base80 + (58472051518553/23293750000000000000000000000 : ℝ)*base81 + (27074431/5000000000000000000000 : ℝ)*base89 + (27074431/5000000000000000000000 : ℝ)*base91 + (27074431/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1647_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89436883/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (23421/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2393/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2429/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4331/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1647_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1647_s2_0 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-807324373/5000000000 : ℝ)*x 0 + (1090433191/2000000000 : ℝ)*x 1 + (5180452201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (807324373/5000000000 : ℝ)^4907 ≤ (9982457163047/100000000000000 : ℝ)^3883 := by
    have hnat : (807324373 : ℕ)^4907*100000000000000^3883 ≤ 9982457163047^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      807324373 5000000000 9982457163047 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090433191/2000000000 : ℝ)^4907 ≤ (23231044938571/50000000000000 : ℝ)^3883 := by
    have hnat : (1090433191 : ℕ)^4907*50000000000000^3883 ≤ 23231044938571^3883*2000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090433191 2000000000 23231044938571 50000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5180452201/10000000000 : ℝ)^4907 ≤ (43555452942381/100000000000000 : ℝ)^3883 := by
    have hnat : (5180452201 : ℕ)^4907*100000000000000^3883 ≤ 43555452942381^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180452201 10000000000 43555452942381 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-807324373/5000000000 : ℝ), (1090433191/2000000000 : ℝ), (5180452201/10000000000 : ℝ)] ![(9982457163047/100000000000000 : ℝ), (23231044938571/50000000000000 : ℝ), (43555452942381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-807324373/5000000000 : ℝ)|^4907 ≤ (9982457163047/100000000000000 : ℝ)^3883
        have hw : |(-807324373/5000000000 : ℝ)|=(807324373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090433191/2000000000 : ℝ)|^4907 ≤ (23231044938571/50000000000000 : ℝ)^3883
        have hw : |(1090433191/2000000000 : ℝ)|=(1090433191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5180452201/10000000000 : ℝ)|^4907 ≤ (43555452942381/100000000000000 : ℝ)^3883
        have hw : |(5180452201/10000000000 : ℝ)|=(5180452201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s2_1 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349202791/10000000000 : ℝ)*x 0 + (-1754647737/10000000000 : ℝ)*x 1 + (5180452951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349202791/10000000000 : ℝ)^4907 ≤ (45356045956939/100000000000000 : ℝ)^3883 := by
    have hnat : (5349202791 : ℕ)^4907*100000000000000^3883 ≤ 45356045956939^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349202791 10000000000 45356045956939 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1754647737/10000000000 : ℝ)^4907 ≤ (11088493115767/100000000000000 : ℝ)^3883 := by
    have hnat : (1754647737 : ℕ)^4907*100000000000000^3883 ≤ 11088493115767^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1754647737 10000000000 11088493115767 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5180452951/10000000000 : ℝ)^4907 ≤ (5444432613879/12500000000000 : ℝ)^3883 := by
    have hnat : (5180452951 : ℕ)^4907*12500000000000^3883 ≤ 5444432613879^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5180452951 10000000000 5444432613879 12500000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349202791/10000000000 : ℝ), (-1754647737/10000000000 : ℝ), (5180452951/10000000000 : ℝ)] ![(45356045956939/100000000000000 : ℝ), (11088493115767/100000000000000 : ℝ), (5444432613879/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349202791/10000000000 : ℝ)|^4907 ≤ (45356045956939/100000000000000 : ℝ)^3883
        have hw : |(5349202791/10000000000 : ℝ)|=(5349202791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1754647737/10000000000 : ℝ)|^4907 ≤ (11088493115767/100000000000000 : ℝ)^3883
        have hw : |(-1754647737/10000000000 : ℝ)|=(1754647737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5180452951/10000000000 : ℝ)|^4907 ≤ (5444432613879/12500000000000 : ℝ)^3883
        have hw : |(5180452951/10000000000 : ℝ)|=(5180452951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s2_2 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334325281/625000000 : ℝ)*x 0 + (2590225863/5000000000 : ℝ)*x 1 + (-43866177/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334325281/625000000 : ℝ)^4907 ≤ (362848513809/800000000000 : ℝ)^3883 := by
    have hnat : (334325281 : ℕ)^4907*800000000000^3883 ≤ 362848513809^3883*625000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334325281 625000000 362848513809 800000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590225863/5000000000 : ℝ)^4907 ≤ (43555447895569/100000000000000 : ℝ)^3883 := by
    have hnat : (2590225863 : ℕ)^4907*100000000000000^3883 ≤ 43555447895569^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590225863 5000000000 43555447895569 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43866177/250000000 : ℝ)^4907 ≤ (11088487868941/100000000000000 : ℝ)^3883 := by
    have hnat : (43866177 : ℕ)^4907*100000000000000^3883 ≤ 11088487868941^3883*250000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43866177 250000000 11088487868941 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334325281/625000000 : ℝ), (2590225863/5000000000 : ℝ), (-43866177/250000000 : ℝ)] ![(362848513809/800000000000 : ℝ), (43555447895569/100000000000000 : ℝ), (11088487868941/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334325281/625000000 : ℝ)|^4907 ≤ (362848513809/800000000000 : ℝ)^3883
        have hw : |(334325281/625000000 : ℝ)|=(334325281/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590225863/5000000000 : ℝ)|^4907 ≤ (43555447895569/100000000000000 : ℝ)^3883
        have hw : |(2590225863/5000000000 : ℝ)|=(2590225863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-43866177/250000000 : ℝ)|^4907 ≤ (11088487868941/100000000000000 : ℝ)^3883
        have hw : |(-43866177/250000000 : ℝ)|=(43866177/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s2_3 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1045634767/2500000000 : ℝ)*x 0 + (3843047797/10000000000 : ℝ)*x 1 + (141980711/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045634767/2500000000 : ℝ)^4907 ≤ (33235986862881/100000000000000 : ℝ)^3883 := by
    have hnat : (1045634767 : ℕ)^4907*100000000000000^3883 ≤ 33235986862881^3883*2500000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045634767 2500000000 33235986862881 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3843047797/10000000000 : ℝ)^4907 ≤ (1493203973217/5000000000000 : ℝ)^3883 := by
    have hnat : (3843047797 : ℕ)^4907*5000000000000^3883 ≤ 1493203973217^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3843047797 10000000000 1493203973217 5000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (141980711/312500000 : ℝ)^4907 ≤ (36899933654169/100000000000000 : ℝ)^3883 := by
    have hnat : (141980711 : ℕ)^4907*100000000000000^3883 ≤ 36899933654169^3883*312500000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141980711 312500000 36899933654169 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1045634767/2500000000 : ℝ), (3843047797/10000000000 : ℝ), (141980711/312500000 : ℝ)] ![(33235986862881/100000000000000 : ℝ), (1493203973217/5000000000000 : ℝ), (36899933654169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1045634767/2500000000 : ℝ)|^4907 ≤ (33235986862881/100000000000000 : ℝ)^3883
        have hw : |(1045634767/2500000000 : ℝ)|=(1045634767/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3843047797/10000000000 : ℝ)|^4907 ≤ (1493203973217/5000000000000 : ℝ)^3883
        have hw : |(3843047797/10000000000 : ℝ)|=(3843047797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(141980711/312500000 : ℝ)|^4907 ≤ (36899933654169/100000000000000 : ℝ)^3883
        have hw : |(141980711/312500000 : ℝ)|=(141980711/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s2_4 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1614717553/10000000000 : ℝ)*x 0 + (5182559781/10000000000 : ℝ)*x 1 + (5450036457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1614717553/10000000000 : ℝ)^4907 ≤ (2495748685769/25000000000000 : ℝ)^3883 := by
    have hnat : (1614717553 : ℕ)^4907*25000000000000^3883 ≤ 2495748685769^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1614717553 10000000000 2495748685769 25000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182559781/10000000000 : ℝ)^4907 ≤ (43577846902159/100000000000000 : ℝ)^3883 := by
    have hnat : (5182559781 : ℕ)^4907*100000000000000^3883 ≤ 43577846902159^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182559781 10000000000 43577846902159 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5450036457/10000000000 : ℝ)^4907 ≤ (46439158337801/100000000000000 : ℝ)^3883 := by
    have hnat : (5450036457 : ℕ)^4907*100000000000000^3883 ≤ 46439158337801^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450036457 10000000000 46439158337801 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1614717553/10000000000 : ℝ), (5182559781/10000000000 : ℝ), (5450036457/10000000000 : ℝ)] ![(2495748685769/25000000000000 : ℝ), (43577846902159/100000000000000 : ℝ), (46439158337801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1614717553/10000000000 : ℝ)|^4907 ≤ (2495748685769/25000000000000 : ℝ)^3883
        have hw : |(-1614717553/10000000000 : ℝ)|=(1614717553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182559781/10000000000 : ℝ)|^4907 ≤ (43577846902159/100000000000000 : ℝ)^3883
        have hw : |(5182559781/10000000000 : ℝ)|=(5182559781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5450036457/10000000000 : ℝ)|^4907 ≤ (46439158337801/100000000000000 : ℝ)^3883
        have hw : |(5450036457/10000000000 : ℝ)|=(5450036457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s2_5 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276636001/10000000000 : ℝ)*x 0 + (-1485063933/10000000000 : ℝ)*x 1 + (2725017847/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276636001/10000000000 : ℝ)^4907 ≤ (44579883638647/100000000000000 : ℝ)^3883 := by
    have hnat : (5276636001 : ℕ)^4907*100000000000000^3883 ≤ 44579883638647^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276636001 10000000000 44579883638647 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1485063933/10000000000 : ℝ)^4907 ≤ (4490483113787/50000000000000 : ℝ)^3883 := by
    have hnat : (1485063933 : ℕ)^4907*50000000000000^3883 ≤ 4490483113787^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1485063933 10000000000 4490483113787 50000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2725017847/5000000000 : ℝ)^4907 ≤ (11609787530461/25000000000000 : ℝ)^3883 := by
    have hnat : (2725017847 : ℕ)^4907*25000000000000^3883 ≤ 11609787530461^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725017847 5000000000 11609787530461 25000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276636001/10000000000 : ℝ), (-1485063933/10000000000 : ℝ), (2725017847/5000000000 : ℝ)] ![(44579883638647/100000000000000 : ℝ), (4490483113787/50000000000000 : ℝ), (11609787530461/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276636001/10000000000 : ℝ)|^4907 ≤ (44579883638647/100000000000000 : ℝ)^3883
        have hw : |(5276636001/10000000000 : ℝ)|=(5276636001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1485063933/10000000000 : ℝ)|^4907 ≤ (4490483113787/50000000000000 : ℝ)^3883
        have hw : |(-1485063933/10000000000 : ℝ)|=(1485063933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2725017847/5000000000 : ℝ)|^4907 ≤ (11609787530461/25000000000000 : ℝ)^3883
        have hw : |(2725017847/5000000000 : ℝ)|=(2725017847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s2_6 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5276636811/10000000000 : ℝ)*x 0 + (2725017637/5000000000 : ℝ)*x 1 + (-742531697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276636811/10000000000 : ℝ)^4907 ≤ (11144973071661/25000000000000 : ℝ)^3883 := by
    have hnat : (5276636811 : ℕ)^4907*25000000000000^3883 ≤ 11144973071661^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276636811 10000000000 11144973071661 25000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2725017637/5000000000 : ℝ)^4907 ≤ (46439145599299/100000000000000 : ℝ)^3883 := by
    have hnat : (2725017637 : ℕ)^4907*100000000000000^3883 ≤ 46439145599299^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725017637 5000000000 46439145599299 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (742531697/5000000000 : ℝ)^4907 ≤ (8980962108351/100000000000000 : ℝ)^3883 := by
    have hnat : (742531697 : ℕ)^4907*100000000000000^3883 ≤ 8980962108351^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      742531697 5000000000 8980962108351 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276636811/10000000000 : ℝ), (2725017637/5000000000 : ℝ), (-742531697/5000000000 : ℝ)] ![(11144973071661/25000000000000 : ℝ), (46439145599299/100000000000000 : ℝ), (8980962108351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276636811/10000000000 : ℝ)|^4907 ≤ (11144973071661/25000000000000 : ℝ)^3883
        have hw : |(5276636811/10000000000 : ℝ)|=(5276636811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2725017637/5000000000 : ℝ)|^4907 ≤ (46439145599299/100000000000000 : ℝ)^3883
        have hw : |(2725017637/5000000000 : ℝ)|=(2725017637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-742531697/5000000000 : ℝ)|^4907 ≤ (8980962108351/100000000000000 : ℝ)^3883
        have hw : |(-742531697/5000000000 : ℝ)|=(742531697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1647_s2_7 (p : ℝ) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4182720107/10000000000 : ℝ)*x 0 + (1134487639/2500000000 : ℝ)*x 1 + (1924269063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4182720107/10000000000 : ℝ)^4907 ≤ (1038681401701/3125000000000 : ℝ)^3883 := by
    have hnat : (4182720107 : ℕ)^4907*3125000000000^3883 ≤ 1038681401701^3883*10000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4182720107 10000000000 1038681401701 3125000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1134487639/2500000000 : ℝ)^4907 ≤ (36844189174453/100000000000000 : ℝ)^3883 := by
    have hnat : (1134487639 : ℕ)^4907*100000000000000^3883 ≤ 36844189174453^3883*2500000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134487639 2500000000 36844189174453 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1924269063/5000000000 : ℝ)^4907 ≤ (29918005954879/100000000000000 : ℝ)^3883 := by
    have hnat : (1924269063 : ℕ)^4907*100000000000000^3883 ≤ 29918005954879^3883*5000000000^4907 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1924269063 5000000000 29918005954879 100000000000000 4907 3883 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4907/1024 : ℝ)) 4907 3883 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4182720107/10000000000 : ℝ), (1134487639/2500000000 : ℝ), (1924269063/5000000000 : ℝ)] ![(1038681401701/3125000000000 : ℝ), (36844189174453/100000000000000 : ℝ), (29918005954879/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4182720107/10000000000 : ℝ)|^4907 ≤ (1038681401701/3125000000000 : ℝ)^3883
        have hw : |(4182720107/10000000000 : ℝ)|=(4182720107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1134487639/2500000000 : ℝ)|^4907 ≤ (36844189174453/100000000000000 : ℝ)^3883
        have hw : |(1134487639/2500000000 : ℝ)|=(1134487639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1924269063/5000000000 : ℝ)|^4907 ≤ (29918005954879/100000000000000 : ℝ)^3883
        have hw : |(1924269063/5000000000 : ℝ)|=(1924269063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1647_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89436883/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4331/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2429/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (10581/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4089/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4331/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2429/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4331/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2429/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4331/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2429/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4331/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2429/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4331/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2429/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4331/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2429/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2429/25000 : ℝ) ^ (4903/1024 : ℝ) ≤ (22172935445401/1562500000000000000 : ℝ) := by
    have hpowers : (2429/25000 : ℝ)^4903 ≤ (22172935445401/1562500000000000000 : ℝ)^1024 := by
      have hnat : (2429 : ℕ)^4903*1562500000000000000^1024 ≤ 22172935445401^1024*25000^4903 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2429 25000 22172935445401 1562500000000000000 4903 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2429/25000 : ℝ)) (X := (22172935445401/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4331/25000 : ℝ) ^ (4903/1024 : ℝ) ≤ (11312329273022497/50000000000000000000 : ℝ) := by
    have hpowers : (4331/25000 : ℝ)^4903 ≤ (11312329273022497/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4331 : ℕ)^4903*50000000000000000000^1024 ≤ 11312329273022497^1024*25000^4903 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4331 25000 11312329273022497 50000000000000000000 4903 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4331/25000 : ℝ)) (X := (11312329273022497/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (781272172935445401/781250000000000000 : ℝ) ≤ (5000029637144269/5000000000000000 : ℝ) ^ (4903/1024 : ℝ) := by
    have hpowers : (781272172935445401/781250000000000000 : ℝ)^1024 ≤ (5000029637144269/5000000000000000 : ℝ)^4903 := by
      have hnat : (781272172935445401 : ℕ)^1024*5000000000000000^4903 ≤ 5000029637144269^4903*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781272172935445401 781250000000000000 5000029637144269 5000000000000000 1024 4903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000029637144269/5000000000000000 : ℝ)) (X := (781272172935445401/781250000000000000 : ℝ)) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50012021863207275329/50000000000000000000 : ℝ) ≤ (1250062763702029/1250000000000000 : ℝ) ^ (4903/1024 : ℝ) := by
    have hpowers : (50012021863207275329/50000000000000000000 : ℝ)^1024 ≤ (1250062763702029/1250000000000000 : ℝ)^4903 := by
      have hnat : (50012021863207275329 : ℕ)^1024*1250000000000000^4903 ≤ 1250062763702029^4903*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012021863207275329 50000000000000000000 1250062763702029 1250000000000000 1024 4903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250062763702029/1250000000000000 : ℝ)) (X := (50012021863207275329/50000000000000000000 : ℝ)) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25011312329273022497/25000000000000000000 : ℝ) ≤ (5000472472471963/5000000000000000 : ℝ) ^ (4903/1024 : ℝ) := by
    have hpowers : (25011312329273022497/25000000000000000000 : ℝ)^1024 ≤ (5000472472471963/5000000000000000 : ℝ)^4903 := by
      have hnat : (25011312329273022497 : ℕ)^1024*5000000000000000^4903 ≤ 5000472472471963^4903*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011312329273022497 25000000000000000000 5000472472471963 5000000000000000 1024 4903 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000472472471963/5000000000000000 : ℝ)) (X := (25011312329273022497/25000000000000000000 : ℝ)) (by norm_num) 4903 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(22172935445401/1562500000000000000 : ℝ) ≤ ((24762970632389143/24765625000000000 : ℝ)+2*(73805887949/126800000000000 : ℝ)*(2429/25000 : ℝ))^(4903/1024 : ℝ) := by
    rw [show (24762970632389143/24765625000000000 : ℝ)+2*(73805887949/126800000000000 : ℝ)*(2429/25000 : ℝ)=(5000029637144269/5000000000000000 : ℝ) by norm_num, show 1+2*(22172935445401/1562500000000000000 : ℝ)=(781272172935445401/781250000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11312329273022497/50000000000000000000 : ℝ)+(22172935445401/1562500000000000000 : ℝ) ≤ ((24762970632389143/24765625000000000 : ℝ)+(73805887949/126800000000000 : ℝ)*((4331/25000 : ℝ)+(2429/25000 : ℝ)))^(4903/1024 : ℝ) := by
    rw [show (24762970632389143/24765625000000000 : ℝ)+(73805887949/126800000000000 : ℝ)*((4331/25000 : ℝ)+(2429/25000 : ℝ))=(1250062763702029/1250000000000000 : ℝ) by norm_num, show 1+(11312329273022497/50000000000000000000 : ℝ)+(22172935445401/1562500000000000000 : ℝ)=(50012021863207275329/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11312329273022497/50000000000000000000 : ℝ) ≤ ((24762970632389143/24765625000000000 : ℝ)+2*(73805887949/126800000000000 : ℝ)*(4331/25000 : ℝ))^(4903/1024 : ℝ) := by
    rw [show (24762970632389143/24765625000000000 : ℝ)+2*(73805887949/126800000000000 : ℝ)*(4331/25000 : ℝ)=(5000472472471963/5000000000000000 : ℝ) by norm_num, show 1+2*(11312329273022497/50000000000000000000 : ℝ)=(25011312329273022497/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (24762970632389143/24765625000000000 : ℝ)*(X 1 0+X 2 0)+(73805887949/126800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4903/1024 : ℝ)) (lo := (2429/25000 : ℝ)) (hi := (4331/25000 : ℝ)) (c := (24762970632389143/24765625000000000 : ℝ)) (alpha := (73805887949/126800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (24762970632389143/24765625000000000 : ℝ)*(X 0 1+X 2 1)+(73805887949/126800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4903/1024 : ℝ)) (lo := (2429/25000 : ℝ)) (hi := (4331/25000 : ℝ)) (c := (24762970632389143/24765625000000000 : ℝ)) (alpha := (73805887949/126800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (24762970632389143/24765625000000000 : ℝ)*(X 0 2+X 1 2)+(73805887949/126800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4903/1024 : ℝ)) (lo := (2429/25000 : ℝ)) (hi := (4331/25000 : ℝ)) (c := (24762970632389143/24765625000000000 : ℝ)) (alpha := (73805887949/126800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-807324373/5000000000 : ℝ)*X 0 0+(1090433191/2000000000 : ℝ)*X 0 1+(5180452201/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349202791/10000000000 : ℝ)*X 1 0+(-1754647737/10000000000 : ℝ)*X 1 1+(5180452951/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334325281/625000000 : ℝ)*X 2 0+(2590225863/5000000000 : ℝ)*X 2 1+(-43866177/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1045634767/2500000000 : ℝ)*X 0 0+(3843047797/10000000000 : ℝ)*X 0 1+(141980711/312500000 : ℝ)*X 0 2+(1045634767/2500000000 : ℝ)*X 1 0+(3843047797/10000000000 : ℝ)*X 1 1+(141980711/312500000 : ℝ)*X 1 2+(1045634767/2500000000 : ℝ)*X 2 0+(3843047797/10000000000 : ℝ)*X 2 1+(141980711/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1614717553/10000000000 : ℝ)*X 0 0+(5182559781/10000000000 : ℝ)*X 0 1+(5450036457/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5276636001/10000000000 : ℝ)*X 1 0+(-1485063933/10000000000 : ℝ)*X 1 1+(2725017847/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5276636811/10000000000 : ℝ)*X 2 0+(2725017637/5000000000 : ℝ)*X 2 1+(-742531697/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4182720107/10000000000 : ℝ)*X 0 0+(1134487639/2500000000 : ℝ)*X 0 1+(1924269063/5000000000 : ℝ)*X 0 2+(4182720107/10000000000 : ℝ)*X 1 0+(1134487639/2500000000 : ℝ)*X 1 1+(1924269063/5000000000 : ℝ)*X 1 2+(4182720107/10000000000 : ℝ)*X 2 0+(1134487639/2500000000 : ℝ)*X 2 1+(1924269063/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1647_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (97798790673555039434397/9906250000000000000000000000 : ℝ) := by norm_num
    linear_combination (1160531891/100000000000000 : ℝ)*(base19) + (63762611/3125000000000 : ℝ)*(base23) + (5986863/12500000000000 : ℝ)*(upper3) + (78421881/50000000000000 : ℝ)*(upper4) + (26378171/5000000000000 : ℝ)*(upper5) + (2554142901043/100000000000 : ℝ)*(major0) + (2554142901043/100000000000 : ℝ)*(major1) + (2554142901043/100000000000 : ℝ)*(major2) + (3680353805147137/100000000000000 : ℝ)*(sp0) + (1840190927345001/50000000000000 : ℝ)*(sp1) + (1840190487409171/50000000000000 : ℝ)*(sp2) + (1427895860392781/100000000000000 : ℝ)*(sp3) + (29210074757/100000000000000 : ℝ)*(sp4) + (1649347553/25000000000000 : ℝ)*(sp7) + (1427902457782993/100000000000000 : ℝ)*(f.failure) + (1840191507610947/50000000000000 : ℝ)*(f.sum) + (1274482736823/317000000000000000000000000 : ℝ)*base66 + (234417406946567/19812500000000000000000000000 : ℝ)*base67 + (269090335031509/39625000000000000000000000000 : ℝ)*base69 + (325270427670509/39625000000000000000000000000 : ℝ)*base71 + (19230815137/63400000000000000000000000 : ℝ)*base74 + (439272521422509/39625000000000000000000000000 : ℝ)*base75 + (219413426939259/39625000000000000000000000000 : ℝ)*base77 + (182871438879067/19812500000000000000000000000 : ℝ)*base79 + (741658584069/158500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (15669181/5000000000000000000000 : ℝ)*base90 + (15669181/5000000000000000000000 : ℝ)*base92 + (15669181/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21148910283366103233297/1585000000000000000000000000 : ℝ) := by norm_num
    linear_combination (661097149/50000000000000 : ℝ)*(base19) + (2814435149/100000000000000 : ℝ)*(base23) + (9623369/25000000000000 : ℝ)*(upper3) + (393930413/100000000000000 : ℝ)*(lower4) + (320736541/100000000000000 : ℝ)*(upper5) + (648644439473553/25000000000000 : ℝ)*(major0) + (648644439473553/25000000000000 : ℝ)*(major1) + (648644439473553/25000000000000 : ℝ)*(major2) + (10306350191/100000000000000 : ℝ)*(sp1) + (22796708137/100000000000000 : ℝ)*(sp2) + (3738647366105527/100000000000000 : ℝ)*(sp4) + (1869317868780519/50000000000000 : ℝ)*(sp5) + (1869310877481121/50000000000000 : ℝ)*(sp6) + (725253852455427/50000000000000 : ℝ)*(sp7) + (725253852455427/50000000000000 : ℝ)*(f.failure) + (3738647366105527/100000000000000 : ℝ)*(f.sum) + (3830516143401/792500000000000000000000000 : ℝ)*base65 + (29492529876383139/9906250000000000000000000000000 : ℝ)*base67 + (28477406403133139/9906250000000000000000000000000 : ℝ)*base69 + (63319311743195639/9906250000000000000000000000000 : ℝ)*base71 + (992495458521/792500000000000000000000000 : ℝ)*base73 + (34425856320554361/9906250000000000000000000000000 : ℝ)*base76 + (42936731510398111/9906250000000000000000000000000 : ℝ)*base78 + (89838248592710611/9906250000000000000000000000000 : ℝ)*base80 + (8559038843637/1585000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (12685959/2500000000000000000000 : ℝ)*base90 + (12685959/2500000000000000000000 : ℝ)*base92 + (12685959/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1647_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89436883/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4331/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2429/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10581/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4089/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1647_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1647_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89436883/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10581/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4089/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1647_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1647_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1647_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4903/1024 : ℝ) ≤ p) (hpb : p ≤ (4907/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (89436883/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10581/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4089/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1647_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
