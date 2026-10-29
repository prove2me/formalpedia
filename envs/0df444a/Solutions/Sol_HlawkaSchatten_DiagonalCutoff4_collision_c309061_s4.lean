-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c309061_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:04:40.551444+00:00
-- url     : https://prove2.me/submissions/ba950625-2d43-4fc0-8d52-4e429ffa6ec3

import Definitions.Def_HlawkaSchatten_DiagonalCutoff4_Localization
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_ordered_majorant
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
theorem raw_linear_data {p k A : ℝ} (hp : 1 ≤ p) (X : Fin 3 → Fin 3 → ℝ)
    (h : RawFrame p k A X) :
    RawLinearData k A X (fun j => lpNorm p (X j))
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

theorem raw_linear_data_bounds {k A T : ℝ} {X : Fin 3 → Fin 3 → ℝ} {N P : Fin 3 → ℝ}
    (h : RawLinearData k A X N P T) (hA : A ≤ 3) :
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



theorem abs_signValue (b : Bool) : |signValue b|=1 := by
  cases b <;> norm_num [signValue]

theorem abs_signedPair (X : Fin 3 → Fin 3 → ℝ) (signs : Fin 3 → Fin 3 → Bool) (i h : Fin 3) :
    |signedPair X signs i h|=|pair X i h| := by
  simp [signedPair,abs_mul,abs_signValue]

theorem chart_majorant {p k A d a rho alpha beta : ℝ}
    (hp : 1 ≤ p) (ha : 0 < a) (hap : a ≤ p)
    (hrho : 0 < rho) (hrho1 : rho ≤ 1) (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta)
    (hcorner1 : 1+rho^a ≤ (1+alpha*rho)^a)
    (hcorner2 : 1+2*rho^a ≤ (1+(alpha+beta)*rho)^a)
    (X : Fin 3 → Fin 3 → ℝ) (orders : Fin 3 → Fin 3 → Fin 3)
    (signs : Fin 3 → Fin 3 → Bool) (hX : OrderedChart p k A d X orders signs)
    (i : Fin 3)
    (hratio : signedPair X signs i (orders i 1) ≤ rho*signedPair X signs i (orders i 0)) :
    lpNorm p (pair X i) ≤ signedPair X signs i (orders i 0)+
      alpha*signedPair X signs i (orders i 1)+beta*signedPair X signs i (orders i 2) := by
  obtain ⟨h2,h21,h10⟩ := hX.ordered i
  have h1 : 0 ≤ signedPair X signs i (orders i 1) := h2.trans h21
  have h0 : 0 ≤ signedPair X signs i (orders i 0) := h1.trans h10
  have hh := ordered_majorant (M := signedPair X signs i (orders i 0))
    (u := signedPair X signs i (orders i 1)) (v := signedPair X signs i (orders i 2)) hp ha hap hrho hrho1 halpha hbeta hcorner1 hcorner2 h0
    (by simpa only [abs_of_nonneg h1,abs_of_nonneg h2] using h21)
    (by simpa only [abs_of_nonneg h1] using hratio)
  have he := HlawkaSchatten.DiagonalRealBundle.lpNorm_eq3 p (pair X i)
    (i := orders i 0) (j := orders i 1) (k := orders i 2)
    ((hX.permutation i).1.ne (by decide)) ((hX.permutation i).1.ne (by decide))
    ((hX.permutation i).1.ne (by decide))
  rw [he]
  calc
    _ ≤ signedPair X signs i (orders i 0)+alpha*|signedPair X signs i (orders i 1)|+
        beta*|signedPair X signs i (orders i 2)| := by
      simpa only [abs_signedPair] using hh
    _ = _ := by rw [abs_of_nonneg h1,abs_of_nonneg h2]

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
theorem collision_support_c309061_s4_s4_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1180036477/5000000000 : ℝ)*x 0 + (452280937/1000000000 : ℝ)*x 1 + (719398959/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1180036477/5000000000 : ℝ)^35 ≤ (3846498465019/25000000000000 : ℝ)^27 := by
    have hnat : (1180036477 : ℕ)^35*25000000000000^27 ≤ 3846498465019^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1180036477 5000000000 3846498465019 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (452280937/1000000000 : ℝ)^35 ≤ (8938137729327/25000000000000 : ℝ)^27 := by
    have hnat : (452280937 : ℕ)^35*25000000000000^27 ≤ 8938137729327^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452280937 1000000000 8938137729327 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (719398959/1250000000 : ℝ)^35 ≤ (24430727601067/50000000000000 : ℝ)^27 := by
    have hnat : (719398959 : ℕ)^35*50000000000000^27 ≤ 24430727601067^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      719398959 1250000000 24430727601067 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1180036477/5000000000 : ℝ), (452280937/1000000000 : ℝ), (719398959/1250000000 : ℝ)] ![(3846498465019/25000000000000 : ℝ), (8938137729327/25000000000000 : ℝ), (24430727601067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1180036477/5000000000 : ℝ)|^35 ≤ (3846498465019/25000000000000 : ℝ)^27
        have hw : |(-1180036477/5000000000 : ℝ)|=(1180036477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(452280937/1000000000 : ℝ)|^35 ≤ (8938137729327/25000000000000 : ℝ)^27
        have hw : |(452280937/1000000000 : ℝ)|=(452280937/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(719398959/1250000000 : ℝ)|^35 ≤ (24430727601067/50000000000000 : ℝ)^27
        have hw : |(719398959/1250000000 : ℝ)|=(719398959/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s4_s4_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1174383341/2500000000 : ℝ)*x 0 + (-2438420431/10000000000 : ℝ)*x 1 + (5529810051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1174383341/2500000000 : ℝ)^35 ≤ (375531292589/1000000000000 : ℝ)^27 := by
    have hnat : (1174383341 : ℕ)^35*1000000000000^27 ≤ 375531292589^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1174383341 2500000000 375531292589 1000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2438420431/10000000000 : ℝ)^35 ≤ (16051334057067/100000000000000 : ℝ)^27 := by
    have hnat : (2438420431 : ℕ)^35*100000000000000^27 ≤ 16051334057067^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2438420431 10000000000 16051334057067 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5529810051/10000000000 : ℝ)^35 ≤ (4639553667527/10000000000000 : ℝ)^27 := by
    have hnat : (5529810051 : ℕ)^35*10000000000000^27 ≤ 4639553667527^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5529810051 10000000000 4639553667527 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1174383341/2500000000 : ℝ), (-2438420431/10000000000 : ℝ), (5529810051/10000000000 : ℝ)] ![(375531292589/1000000000000 : ℝ), (16051334057067/100000000000000 : ℝ), (4639553667527/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1174383341/2500000000 : ℝ)|^35 ≤ (375531292589/1000000000000 : ℝ)^27
        have hw : |(1174383341/2500000000 : ℝ)|=(1174383341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2438420431/10000000000 : ℝ)|^35 ≤ (16051334057067/100000000000000 : ℝ)^27
        have hw : |(-2438420431/10000000000 : ℝ)|=(2438420431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5529810051/10000000000 : ℝ)|^35 ≤ (4639553667527/10000000000000 : ℝ)^27
        have hw : |(5529810051/10000000000 : ℝ)|=(5529810051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s4_s4_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4750930263/10000000000 : ℝ)*x 0 + (383390271/625000000 : ℝ)*x 1 + (-1536315831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4750930263/10000000000 : ℝ)^35 ≤ (38107404366819/100000000000000 : ℝ)^27 := by
    have hnat : (4750930263 : ℕ)^35*100000000000000^27 ≤ 38107404366819^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4750930263 10000000000 38107404366819 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (383390271/625000000 : ℝ)^35 ≤ (53073222981619/100000000000000 : ℝ)^27 := by
    have hnat : (383390271 : ℕ)^35*100000000000000^27 ≤ 53073222981619^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383390271 625000000 53073222981619 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1536315831/10000000000 : ℝ)^35 ≤ (8819372633471/100000000000000 : ℝ)^27 := by
    have hnat : (1536315831 : ℕ)^35*100000000000000^27 ≤ 8819372633471^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1536315831 10000000000 8819372633471 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4750930263/10000000000 : ℝ), (383390271/625000000 : ℝ), (-1536315831/10000000000 : ℝ)] ![(38107404366819/100000000000000 : ℝ), (53073222981619/100000000000000 : ℝ), (8819372633471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4750930263/10000000000 : ℝ)|^35 ≤ (38107404366819/100000000000000 : ℝ)^27
        have hw : |(4750930263/10000000000 : ℝ)|=(4750930263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(383390271/625000000 : ℝ)|^35 ≤ (53073222981619/100000000000000 : ℝ)^27
        have hw : |(383390271/625000000 : ℝ)|=(383390271/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1536315831/10000000000 : ℝ)|^35 ≤ (8819372633471/100000000000000 : ℝ)^27
        have hw : |(-1536315831/10000000000 : ℝ)|=(1536315831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s4_s4_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (591808543/1000000000 : ℝ)*x 0 + (386497819/1250000000 : ℝ)*x 1 + (3694023537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (591808543/1000000000 : ℝ)^35 ≤ (25330827456139/50000000000000 : ℝ)^27 := by
    have hnat : (591808543 : ℕ)^35*50000000000000^27 ≤ 25330827456139^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      591808543 1000000000 25330827456139 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (386497819/1250000000 : ℝ)^35 ≤ (4367431997107/20000000000000 : ℝ)^27 := by
    have hnat : (386497819 : ℕ)^35*20000000000000^27 ≤ 4367431997107^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386497819 1250000000 4367431997107 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3694023537/10000000000 : ℝ)^35 ≤ (13750592541593/50000000000000 : ℝ)^27 := by
    have hnat : (3694023537 : ℕ)^35*50000000000000^27 ≤ 13750592541593^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3694023537 10000000000 13750592541593 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(591808543/1000000000 : ℝ), (386497819/1250000000 : ℝ), (3694023537/10000000000 : ℝ)] ![(25330827456139/50000000000000 : ℝ), (4367431997107/20000000000000 : ℝ), (13750592541593/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(591808543/1000000000 : ℝ)|^35 ≤ (25330827456139/50000000000000 : ℝ)^27
        have hw : |(591808543/1000000000 : ℝ)|=(591808543/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(386497819/1250000000 : ℝ)|^35 ≤ (4367431997107/20000000000000 : ℝ)^27
        have hw : |(386497819/1250000000 : ℝ)|=(386497819/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3694023537/10000000000 : ℝ)|^35 ≤ (13750592541593/50000000000000 : ℝ)^27
        have hw : |(3694023537/10000000000 : ℝ)|=(3694023537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s4_s4_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2366041723/10000000000 : ℝ)*x 0 + (3981723197/10000000000 : ℝ)*x 1 + (6239295913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2366041723/10000000000 : ℝ)^35 ≤ (7718227192913/50000000000000 : ℝ)^27 := by
    have hnat : (2366041723 : ℕ)^35*50000000000000^27 ≤ 7718227192913^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2366041723 10000000000 7718227192913 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3981723197/10000000000 : ℝ)^35 ≤ (3788642407521/12500000000000 : ℝ)^27 := by
    have hnat : (3981723197 : ℕ)^35*12500000000000^27 ≤ 3788642407521^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3981723197 10000000000 3788642407521 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6239295913/10000000000 : ℝ)^35 ≤ (54254406336067/100000000000000 : ℝ)^27 := by
    have hnat : (6239295913 : ℕ)^35*100000000000000^27 ≤ 54254406336067^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6239295913 10000000000 54254406336067 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2366041723/10000000000 : ℝ), (3981723197/10000000000 : ℝ), (6239295913/10000000000 : ℝ)] ![(7718227192913/50000000000000 : ℝ), (3788642407521/12500000000000 : ℝ), (54254406336067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2366041723/10000000000 : ℝ)|^35 ≤ (7718227192913/50000000000000 : ℝ)^27
        have hw : |(-2366041723/10000000000 : ℝ)|=(2366041723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3981723197/10000000000 : ℝ)|^35 ≤ (3788642407521/12500000000000 : ℝ)^27
        have hw : |(3981723197/10000000000 : ℝ)|=(3981723197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6239295913/10000000000 : ℝ)|^35 ≤ (54254406336067/100000000000000 : ℝ)^27
        have hw : |(6239295913/10000000000 : ℝ)|=(6239295913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s4_s4_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (878620559/2000000000 : ℝ)*x 0 + (-97517973/500000000 : ℝ)*x 1 + (6177101/10000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (878620559/2000000000 : ℝ)^35 ≤ (6885822760227/20000000000000 : ℝ)^27 := by
    have hnat : (878620559 : ℕ)^35*20000000000000^27 ≤ 6885822760227^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      878620559 2000000000 6885822760227 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (97517973/500000000 : ℝ)^35 ≤ (12016507572351/100000000000000 : ℝ)^27 := by
    have hnat : (97517973 : ℕ)^35*100000000000000^27 ≤ 12016507572351^27*500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97517973 500000000 12016507572351 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6177101/10000000 : ℝ)^35 ≤ (13388594654023/25000000000000 : ℝ)^27 := by
    have hnat : (6177101 : ℕ)^35*25000000000000^27 ≤ 13388594654023^27*10000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6177101 10000000 13388594654023 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(878620559/2000000000 : ℝ), (-97517973/500000000 : ℝ), (6177101/10000000 : ℝ)] ![(6885822760227/20000000000000 : ℝ), (12016507572351/100000000000000 : ℝ), (13388594654023/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(878620559/2000000000 : ℝ)|^35 ≤ (6885822760227/20000000000000 : ℝ)^27
        have hw : |(878620559/2000000000 : ℝ)|=(878620559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-97517973/500000000 : ℝ)|^35 ≤ (12016507572351/100000000000000 : ℝ)^27
        have hw : |(-97517973/500000000 : ℝ)|=(97517973/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6177101/10000000 : ℝ)|^35 ≤ (13388594654023/25000000000000 : ℝ)^27
        have hw : |(6177101/10000000 : ℝ)|=(6177101/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s4_s4_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2223385157/5000000000 : ℝ)*x 0 + (1356545387/2000000000 : ℝ)*x 1 + (-924731879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2223385157/5000000000 : ℝ)^35 ≤ (3497531585289/10000000000000 : ℝ)^27 := by
    have hnat : (2223385157 : ℕ)^35*10000000000000^27 ≤ 3497531585289^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2223385157 5000000000 3497531585289 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1356545387/2000000000 : ℝ)^35 ≤ (472324085001/781250000000 : ℝ)^27 := by
    have hnat : (1356545387 : ℕ)^35*781250000000^27 ≤ 472324085001^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1356545387 2000000000 472324085001 781250000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (924731879/10000000000 : ℝ)^35 ≤ (4567201257313/100000000000000 : ℝ)^27 := by
    have hnat : (924731879 : ℕ)^35*100000000000000^27 ≤ 4567201257313^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924731879 10000000000 4567201257313 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2223385157/5000000000 : ℝ), (1356545387/2000000000 : ℝ), (-924731879/10000000000 : ℝ)] ![(3497531585289/10000000000000 : ℝ), (472324085001/781250000000 : ℝ), (4567201257313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2223385157/5000000000 : ℝ)|^35 ≤ (3497531585289/10000000000000 : ℝ)^27
        have hw : |(2223385157/5000000000 : ℝ)|=(2223385157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1356545387/2000000000 : ℝ)|^35 ≤ (472324085001/781250000000 : ℝ)^27
        have hw : |(1356545387/2000000000 : ℝ)|=(1356545387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-924731879/10000000000 : ℝ)|^35 ≤ (4567201257313/100000000000000 : ℝ)^27
        have hw : |(-924731879/10000000000 : ℝ)|=(924731879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s4_s4_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1181013413/2000000000 : ℝ)*x 0 + (813660179/2000000000 : ℝ)*x 1 + (2699834179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1181013413/2000000000 : ℝ)^35 ≤ (6314654783983/12500000000000 : ℝ)^27 := by
    have hnat : (1181013413 : ℕ)^35*12500000000000^27 ≤ 6314654783983^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1181013413 2000000000 6314654783983 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (813660179/2000000000 : ℝ)^35 ≤ (31166182136167/100000000000000 : ℝ)^27 := by
    have hnat : (813660179 : ℕ)^35*100000000000000^27 ≤ 31166182136167^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      813660179 2000000000 31166182136167 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699834179/10000000000 : ℝ)^35 ≤ (2289572448159/12500000000000 : ℝ)^27 := by
    have hnat : (2699834179 : ℕ)^35*12500000000000^27 ≤ 2289572448159^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699834179 10000000000 2289572448159 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1181013413/2000000000 : ℝ), (813660179/2000000000 : ℝ), (2699834179/10000000000 : ℝ)] ![(6314654783983/12500000000000 : ℝ), (31166182136167/100000000000000 : ℝ), (2289572448159/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1181013413/2000000000 : ℝ)|^35 ≤ (6314654783983/12500000000000 : ℝ)^27
        have hw : |(1181013413/2000000000 : ℝ)|=(1181013413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(813660179/2000000000 : ℝ)|^35 ≤ (31166182136167/100000000000000 : ℝ)^27
        have hw : |(813660179/2000000000 : ℝ)|=(813660179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699834179/10000000000 : ℝ)|^35 ≤ (2289572448159/12500000000000 : ℝ)^27
        have hw : |(2699834179/10000000000 : ℝ)|=(2699834179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s4_s4_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1572349419/10000000000 : ℝ)*x 0 + (4612297173/10000000000 : ℝ)*x 1 + (3118979403/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1572349419/10000000000 : ℝ)^35 ≤ (9088443843287/100000000000000 : ℝ)^27 := by
    have hnat : (1572349419 : ℕ)^35*100000000000000^27 ≤ 9088443843287^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1572349419 10000000000 9088443843287 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4612297173/10000000000 : ℝ)^35 ≤ (7334444257729/20000000000000 : ℝ)^27 := by
    have hnat : (4612297173 : ℕ)^35*20000000000000^27 ≤ 7334444257729^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4612297173 10000000000 7334444257729 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3118979403/5000000000 : ℝ)^35 ≤ (54239334849683/100000000000000 : ℝ)^27 := by
    have hnat : (3118979403 : ℕ)^35*100000000000000^27 ≤ 54239334849683^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3118979403 5000000000 54239334849683 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1572349419/10000000000 : ℝ), (4612297173/10000000000 : ℝ), (3118979403/5000000000 : ℝ)] ![(9088443843287/100000000000000 : ℝ), (7334444257729/20000000000000 : ℝ), (54239334849683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1572349419/10000000000 : ℝ)|^35 ≤ (9088443843287/100000000000000 : ℝ)^27
        have hw : |(-1572349419/10000000000 : ℝ)|=(1572349419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4612297173/10000000000 : ℝ)|^35 ≤ (7334444257729/20000000000000 : ℝ)^27
        have hw : |(4612297173/10000000000 : ℝ)|=(4612297173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3118979403/5000000000 : ℝ)|^35 ≤ (54239334849683/100000000000000 : ℝ)^27
        have hw : |(3118979403/5000000000 : ℝ)|=(3118979403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s4_s4_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4244749037/10000000000 : ℝ)*x 0 + (-213739691/1000000000 : ℝ)*x 1 + (3087881993/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4244749037/10000000000 : ℝ)^35 ≤ (658591233519/2000000000000 : ℝ)^27 := by
    have hnat : (4244749037 : ℕ)^35*2000000000000^27 ≤ 658591233519^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244749037 10000000000 658591233519 2000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (213739691/1000000000 : ℝ)^35 ≤ (1691385683021/12500000000000 : ℝ)^27 := by
    have hnat : (213739691 : ℕ)^35*12500000000000^27 ≤ 1691385683021^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213739691 1000000000 1691385683021 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3087881993/5000000000 : ℝ)^35 ≤ (53539352851167/100000000000000 : ℝ)^27 := by
    have hnat : (3087881993 : ℕ)^35*100000000000000^27 ≤ 53539352851167^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3087881993 5000000000 53539352851167 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4244749037/10000000000 : ℝ), (-213739691/1000000000 : ℝ), (3087881993/5000000000 : ℝ)] ![(658591233519/2000000000000 : ℝ), (1691385683021/12500000000000 : ℝ), (53539352851167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4244749037/10000000000 : ℝ)|^35 ≤ (658591233519/2000000000000 : ℝ)^27
        have hw : |(4244749037/10000000000 : ℝ)|=(4244749037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-213739691/1000000000 : ℝ)|^35 ≤ (1691385683021/12500000000000 : ℝ)^27
        have hw : |(-213739691/1000000000 : ℝ)|=(213739691/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3087881993/5000000000 : ℝ)|^35 ≤ (53539352851167/100000000000000 : ℝ)^27
        have hw : |(3087881993/5000000000 : ℝ)|=(3087881993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s4_s4_16 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (34841163/62500000 : ℝ)*x 0 + (5726063887/10000000000 : ℝ)*x 1 + (-463034653/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34841163/62500000 : ℝ)^35 ≤ (23441552521139/50000000000000 : ℝ)^27 := by
    have hnat : (34841163 : ℕ)^35*50000000000000^27 ≤ 23441552521139^27*62500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34841163 62500000 23441552521139 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5726063887/10000000000 : ℝ)^35 ≤ (24270564596559/50000000000000 : ℝ)^27 := by
    have hnat : (5726063887 : ℕ)^35*50000000000000^27 ≤ 24270564596559^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5726063887 10000000000 24270564596559 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (463034653/5000000000 : ℝ)^35 ≤ (4575765751107/100000000000000 : ℝ)^27 := by
    have hnat : (463034653 : ℕ)^35*100000000000000^27 ≤ 4575765751107^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      463034653 5000000000 4575765751107 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(34841163/62500000 : ℝ), (5726063887/10000000000 : ℝ), (-463034653/5000000000 : ℝ)] ![(23441552521139/50000000000000 : ℝ), (24270564596559/50000000000000 : ℝ), (4575765751107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(34841163/62500000 : ℝ)|^35 ≤ (23441552521139/50000000000000 : ℝ)^27
        have hw : |(34841163/62500000 : ℝ)|=(34841163/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5726063887/10000000000 : ℝ)|^35 ≤ (24270564596559/50000000000000 : ℝ)^27
        have hw : |(5726063887/10000000000 : ℝ)|=(5726063887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-463034653/5000000000 : ℝ)|^35 ≤ (4575765751107/100000000000000 : ℝ)^27
        have hw : |(-463034653/5000000000 : ℝ)|=(463034653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s4_s4_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (695925287/1000000000 : ℝ)*x 0 + (2794428081/10000000000 : ℝ)*x 1 + (1351377289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (695925287/1000000000 : ℝ)^35 ≤ (1953280099911/3125000000000 : ℝ)^27 := by
    have hnat : (695925287 : ℕ)^35*3125000000000^27 ≤ 1953280099911^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      695925287 1000000000 1953280099911 3125000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2794428081/10000000000 : ℝ)^35 ≤ (19152769621487/100000000000000 : ℝ)^27 := by
    have hnat : (2794428081 : ℕ)^35*100000000000000^27 ≤ 19152769621487^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2794428081 10000000000 19152769621487 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351377289/5000000000 : ℝ)^35 ≤ (18342267173477/100000000000000 : ℝ)^27 := by
    have hnat : (1351377289 : ℕ)^35*100000000000000^27 ≤ 18342267173477^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351377289 5000000000 18342267173477 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(695925287/1000000000 : ℝ), (2794428081/10000000000 : ℝ), (1351377289/5000000000 : ℝ)] ![(1953280099911/3125000000000 : ℝ), (19152769621487/100000000000000 : ℝ), (18342267173477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(695925287/1000000000 : ℝ)|^35 ≤ (1953280099911/3125000000000 : ℝ)^27
        have hw : |(695925287/1000000000 : ℝ)|=(695925287/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2794428081/10000000000 : ℝ)|^35 ≤ (19152769621487/100000000000000 : ℝ)^27
        have hw : |(2794428081/10000000000 : ℝ)|=(2794428081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351377289/5000000000 : ℝ)|^35 ≤ (18342267173477/100000000000000 : ℝ)^27
        have hw : |(1351377289/5000000000 : ℝ)|=(1351377289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s4_s4_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-311084261/2000000000 : ℝ)*x 0 + (635268307/1250000000 : ℝ)*x 1 + (5808769173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (311084261/2000000000 : ℝ)^35 ≤ (8961807513899/100000000000000 : ℝ)^27 := by
    have hnat : (311084261 : ℕ)^35*100000000000000^27 ≤ 8961807513899^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311084261 2000000000 8961807513899 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (635268307/1250000000 : ℝ)^35 ≤ (41586277126169/100000000000000 : ℝ)^27 := by
    have hnat : (635268307 : ℕ)^35*100000000000000^27 ≤ 41586277126169^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      635268307 1250000000 41586277126169 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5808769173/10000000000 : ℝ)^35 ≤ (6181489418939/12500000000000 : ℝ)^27 := by
    have hnat : (5808769173 : ℕ)^35*12500000000000^27 ≤ 6181489418939^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5808769173 10000000000 6181489418939 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-311084261/2000000000 : ℝ), (635268307/1250000000 : ℝ), (5808769173/10000000000 : ℝ)] ![(8961807513899/100000000000000 : ℝ), (41586277126169/100000000000000 : ℝ), (6181489418939/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-311084261/2000000000 : ℝ)|^35 ≤ (8961807513899/100000000000000 : ℝ)^27
        have hw : |(-311084261/2000000000 : ℝ)|=(311084261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(635268307/1250000000 : ℝ)|^35 ≤ (41586277126169/100000000000000 : ℝ)^27
        have hw : |(635268307/1250000000 : ℝ)|=(635268307/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5808769173/10000000000 : ℝ)|^35 ≤ (6181489418939/12500000000000 : ℝ)^27
        have hw : |(5808769173/10000000000 : ℝ)|=(5808769173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s4_s4_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5537846403/10000000000 : ℝ)*x 0 + (-817845727/5000000000 : ℝ)*x 1 + (5303679611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5537846403/10000000000 : ℝ)^35 ≤ (1162073976667/2500000000000 : ℝ)^27 := by
    have hnat : (5537846403 : ℕ)^35*2500000000000^27 ≤ 1162073976667^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5537846403 10000000000 1162073976667 2500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (817845727/5000000000 : ℝ)^35 ≤ (382634396997/4000000000000 : ℝ)^27 := by
    have hnat : (817845727 : ℕ)^35*4000000000000^27 ≤ 382634396997^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      817845727 5000000000 382634396997 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5303679611/10000000000 : ℝ)^35 ≤ (5493897625477/12500000000000 : ℝ)^27 := by
    have hnat : (5303679611 : ℕ)^35*12500000000000^27 ≤ 5493897625477^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5303679611 10000000000 5493897625477 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5537846403/10000000000 : ℝ), (-817845727/5000000000 : ℝ), (5303679611/10000000000 : ℝ)] ![(1162073976667/2500000000000 : ℝ), (382634396997/4000000000000 : ℝ), (5493897625477/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5537846403/10000000000 : ℝ)|^35 ≤ (1162073976667/2500000000000 : ℝ)^27
        have hw : |(5537846403/10000000000 : ℝ)|=(5537846403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-817845727/5000000000 : ℝ)|^35 ≤ (382634396997/4000000000000 : ℝ)^27
        have hw : |(-817845727/5000000000 : ℝ)|=(817845727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5303679611/10000000000 : ℝ)|^35 ≤ (5493897625477/12500000000000 : ℝ)^27
        have hw : |(5303679611/10000000000 : ℝ)|=(5303679611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s4_s4_23 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (263451823/625000000 : ℝ)*x 0 + (671102539/1000000000 : ℝ)*x 1 + (-1388671077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (263451823/625000000 : ℝ)^35 ≤ (1305320295039/4000000000000 : ℝ)^27 := by
    have hnat : (263451823 : ℕ)^35*4000000000000^27 ≤ 1305320295039^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263451823 625000000 1305320295039 4000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (671102539/1000000000 : ℝ)^35 ≤ (11926062055151/20000000000000 : ℝ)^27 := by
    have hnat : (671102539 : ℕ)^35*20000000000000^27 ≤ 11926062055151^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671102539 1000000000 11926062055151 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1388671077/10000000000 : ℝ)^35 ≤ (7736682331191/100000000000000 : ℝ)^27 := by
    have hnat : (1388671077 : ℕ)^35*100000000000000^27 ≤ 7736682331191^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1388671077 10000000000 7736682331191 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(263451823/625000000 : ℝ), (671102539/1000000000 : ℝ), (-1388671077/10000000000 : ℝ)] ![(1305320295039/4000000000000 : ℝ), (11926062055151/20000000000000 : ℝ), (7736682331191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(263451823/625000000 : ℝ)|^35 ≤ (1305320295039/4000000000000 : ℝ)^27
        have hw : |(263451823/625000000 : ℝ)|=(263451823/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(671102539/1000000000 : ℝ)|^35 ≤ (11926062055151/20000000000000 : ℝ)^27
        have hw : |(671102539/1000000000 : ℝ)|=(671102539/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1388671077/10000000000 : ℝ)|^35 ≤ (7736682331191/100000000000000 : ℝ)^27
        have hw : |(-1388671077/10000000000 : ℝ)|=(1388671077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309061_s4_s4_27 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7141012889/10000000000 : ℝ)*x 0 + (2508138787/10000000000 : ℝ)*x 1 + (2745813117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7141012889/10000000000 : ℝ)^35 ≤ (32314645552807/50000000000000 : ℝ)^27 := by
    have hnat : (7141012889 : ℕ)^35*50000000000000^27 ≤ 32314645552807^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7141012889 10000000000 32314645552807 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2508138787/10000000000 : ℝ)^35 ≤ (16648750980461/100000000000000 : ℝ)^27 := by
    have hnat : (2508138787 : ℕ)^35*100000000000000^27 ≤ 16648750980461^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2508138787 10000000000 16648750980461 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2745813117/10000000000 : ℝ)^35 ≤ (4680489475421/25000000000000 : ℝ)^27 := by
    have hnat : (2745813117 : ℕ)^35*25000000000000^27 ≤ 4680489475421^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745813117 10000000000 4680489475421 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7141012889/10000000000 : ℝ), (2508138787/10000000000 : ℝ), (2745813117/10000000000 : ℝ)] ![(32314645552807/50000000000000 : ℝ), (16648750980461/100000000000000 : ℝ), (4680489475421/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7141012889/10000000000 : ℝ)|^35 ≤ (32314645552807/50000000000000 : ℝ)^27
        have hw : |(7141012889/10000000000 : ℝ)|=(7141012889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2508138787/10000000000 : ℝ)|^35 ≤ (16648750980461/100000000000000 : ℝ)^27
        have hw : |(2508138787/10000000000 : ℝ)|=(2508138787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2745813117/10000000000 : ℝ)|^35 ≤ (4680489475421/25000000000000 : ℝ)^27
        have hw : |(2745813117/10000000000 : ℝ)|=(2745813117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309061_s4 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((23017/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(23017/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(52481/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(52481/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4751/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4751/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5439/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5439/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32209/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(32209/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29753/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(29753/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (77509/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (77509/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base62 : ((-1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).1]
  have base63 : ((1 : ℝ)*X 0 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 0).2]
  have base64 : ((-1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).1]
  have base65 : ((1 : ℝ)*X 0 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 1).2]
  have base66 : ((-1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).1]
  have base67 : ((1 : ℝ)*X 0 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 0 2).2]
  have base68 : ((-1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).1]
  have base69 : ((1 : ℝ)*X 1 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 0).2]
  have base70 : ((-1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).1]
  have base71 : ((1 : ℝ)*X 1 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 1).2]
  have base72 : ((-1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).1]
  have base73 : ((1 : ℝ)*X 1 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 1 2).2]
  have base74 : ((-1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).1]
  have base75 : ((1 : ℝ)*X 2 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 0).2]
  have base76 : ((-1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).1]
  have base77 : ((1 : ℝ)*X 2 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 1).2]
  have base78 : ((-1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).1]
  have base79 : ((1 : ℝ)*X 2 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.1 2 2).2]
  have base80 : ((-1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).1]
  have base81 : ((1 : ℝ)*N 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 0).2]
  have base82 : ((-1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).1]
  have base83 : ((1 : ℝ)*N 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 1).2]
  have base84 : ((-1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).1]
  have base85 : ((1 : ℝ)*N 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.1 2).2]
  have base86 : ((-1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).1]
  have base87 : ((1 : ℝ)*P 0) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 0).2]
  have base88 : ((-1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).1]
  have base89 : ((1 : ℝ)*P 1) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 1).2]
  have base90 : ((-1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).1]
  have base91 : ((1 : ℝ)*P 2) ≤ (3 : ℝ) := by
    linarith only [(bounds.2.2.1 2).2]
  have base92 : ((-1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.1]
  have base93 : ((1 : ℝ)*T) ≤ (3 : ℝ) := by
    linarith only [bounds.2.2.2.2]
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (23017/50000 : ℝ) ^ (69/16 : ℝ) ≤ (176196369575730029/5000000000000000000 : ℝ) := by
    have hpowers : (23017/50000 : ℝ)^69 ≤ (176196369575730029/5000000000000000000 : ℝ)^16 := by
      have hnat : (23017 : ℕ)^69*5000000000000000000^16 ≤ 176196369575730029^16*50000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        23017 50000 176196369575730029 5000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (23017/50000 : ℝ)) (X := (176196369575730029/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s4_corner0a : (5176196369575730029/5000000000000000000 : ℝ) ≤ (10080630766913103/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (5176196369575730029/5000000000000000000 : ℝ)^16 ≤ (10080630766913103/10000000000000000 : ℝ)^69 := by
      have hnat : (5176196369575730029 : ℕ)^16*10000000000000000^69 ≤ 10080630766913103^69*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5176196369575730029 5000000000000000000 10080630766913103 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10080630766913103/10000000000000000 : ℝ)) (X := (5176196369575730029/5000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s4_corner0b : (2676196369575730029/2500000000000000000 : ℝ) ≤ (10159180097449123/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (2676196369575730029/2500000000000000000 : ℝ)^16 ≤ (10159180097449123/10000000000000000 : ℝ)^69 := by
      have hnat : (2676196369575730029 : ℕ)^16*10000000000000000^69 ≤ 10159180097449123^69*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2676196369575730029 2500000000000000000 10159180097449123 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10159180097449123/10000000000000000 : ℝ)) (X := (2676196369575730029/2500000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(80630766913103/4603400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(3927466526801/230170000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (23017/50000 : ℝ)) (alpha := (80630766913103/4603400000000000 : ℝ)) (beta := (3927466526801/230170000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (23017/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(80630766913103/4603400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(3927466526801/230170000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (52481/100000 : ℝ) ^ (69/16 : ℝ) ≤ (77520948289425861/1250000000000000000 : ℝ) := by
    have hpowers : (52481/100000 : ℝ)^69 ≤ (77520948289425861/1250000000000000000 : ℝ)^16 := by
      have hnat : (52481 : ℕ)^69*1250000000000000000^16 ≤ 77520948289425861^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52481 100000 77520948289425861 1250000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (52481/100000 : ℝ)) (X := (77520948289425861/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s4_corner1a : (1327520948289425861/1250000000000000000 : ℝ) ≤ (10140501838160161/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (1327520948289425861/1250000000000000000 : ℝ)^16 ≤ (10140501838160161/10000000000000000 : ℝ)^69 := by
      have hnat : (1327520948289425861 : ℕ)^16*10000000000000000^69 ≤ 10140501838160161^69*1250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1327520948289425861 1250000000000000000 10140501838160161 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10140501838160161/10000000000000000 : ℝ)) (X := (1327520948289425861/1250000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s4_corner1b : (702520948289425861/625000000000000000 : ℝ) ≤ (2054967212013041/2000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (702520948289425861/625000000000000000 : ℝ)^16 ≤ (2054967212013041/2000000000000000 : ℝ)^69 := by
      have hnat : (702520948289425861 : ℕ)^16*2000000000000000^69 ≤ 2054967212013041^69*625000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        702520948289425861 625000000000000000 2054967212013041 2000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2054967212013041/2000000000000000 : ℝ)) (X := (702520948289425861/625000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(140501838160161/5248100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(33583555476261/1312025000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (52481/100000 : ℝ)) (alpha := (140501838160161/5248100000000000 : ℝ)) (beta := (33583555476261/1312025000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (52481/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(140501838160161/5248100000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(33583555476261/1312025000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (4751/10000 : ℝ) ^ (69/16 : ℝ) ≤ (2018856488662481613/50000000000000000000 : ℝ) := by
    have hpowers : (4751/10000 : ℝ)^69 ≤ (2018856488662481613/50000000000000000000 : ℝ)^16 := by
      have hnat : (4751 : ℕ)^69*50000000000000000000^16 ≤ 2018856488662481613^16*10000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4751 10000 2018856488662481613 50000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4751/10000 : ℝ)) (X := (2018856488662481613/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s4_corner2a : (52018856488662481613/50000000000000000000 : ℝ) ≤ (504610491752971/500000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (52018856488662481613/50000000000000000000 : ℝ)^16 ≤ (504610491752971/500000000000000 : ℝ)^69 := by
      have hnat : (52018856488662481613 : ℕ)^16*500000000000000^69 ≤ 504610491752971^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52018856488662481613 50000000000000000000 504610491752971 500000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (504610491752971/500000000000000 : ℝ)) (X := (52018856488662481613/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s4_corner2b : (27018856488662481613/25000000000000000000 : ℝ) ≤ (5090855237775091/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (27018856488662481613/25000000000000000000 : ℝ)^16 ≤ (5090855237775091/5000000000000000 : ℝ)^69 := by
      have hnat : (27018856488662481613 : ℕ)^16*5000000000000000^69 ≤ 5090855237775091^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27018856488662481613 25000000000000000000 5090855237775091 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5090855237775091/5000000000000000 : ℝ)) (X := (27018856488662481613/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(4610491752971/237550000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(44750320245381/2375500000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (4751/10000 : ℝ)) (alpha := (4610491752971/237550000000000 : ℝ)) (beta := (44750320245381/2375500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (4751/10000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(4610491752971/237550000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(44750320245381/2375500000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-1180036477/5000000000 : ℝ)*X 0 0+(452280937/1000000000 : ℝ)*X 0 1+(719398959/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_1 : ((1174383341/2500000000 : ℝ)*X 1 0+(-2438420431/10000000000 : ℝ)*X 1 1+(5529810051/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s4_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_2 : ((4750930263/10000000000 : ℝ)*X 2 0+(383390271/625000000 : ℝ)*X 2 1+(-1536315831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_6 : ((591808543/1000000000 : ℝ)*X 0 0+(386497819/1250000000 : ℝ)*X 0 1+(3694023537/10000000000 : ℝ)*X 0 2+(591808543/1000000000 : ℝ)*X 1 0+(386497819/1250000000 : ℝ)*X 1 1+(3694023537/10000000000 : ℝ)*X 1 2+(591808543/1000000000 : ℝ)*X 2 0+(386497819/1250000000 : ℝ)*X 2 1+(3694023537/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s4_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-2366041723/10000000000 : ℝ)*X 0 0+(3981723197/10000000000 : ℝ)*X 0 1+(6239295913/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((878620559/2000000000 : ℝ)*X 1 0+(-97517973/500000000 : ℝ)*X 1 1+(6177101/10000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((2223385157/5000000000 : ℝ)*X 2 0+(1356545387/2000000000 : ℝ)*X 2 1+(-924731879/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((1181013413/2000000000 : ℝ)*X 0 0+(813660179/2000000000 : ℝ)*X 0 1+(2699834179/10000000000 : ℝ)*X 0 2+(1181013413/2000000000 : ℝ)*X 1 0+(813660179/2000000000 : ℝ)*X 1 1+(2699834179/10000000000 : ℝ)*X 1 2+(1181013413/2000000000 : ℝ)*X 2 0+(813660179/2000000000 : ℝ)*X 2 1+(2699834179/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-1572349419/10000000000 : ℝ)*X 0 0+(4612297173/10000000000 : ℝ)*X 0 1+(3118979403/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((4244749037/10000000000 : ℝ)*X 1 0+(-213739691/1000000000 : ℝ)*X 1 1+(3087881993/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((34841163/62500000 : ℝ)*X 2 0+(5726063887/10000000000 : ℝ)*X 2 1+(-463034653/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((695925287/1000000000 : ℝ)*X 0 0+(2794428081/10000000000 : ℝ)*X 0 1+(1351377289/5000000000 : ℝ)*X 0 2+(695925287/1000000000 : ℝ)*X 1 0+(2794428081/10000000000 : ℝ)*X 1 1+(1351377289/5000000000 : ℝ)*X 1 2+(695925287/1000000000 : ℝ)*X 2 0+(2794428081/10000000000 : ℝ)*X 2 1+(1351377289/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-311084261/2000000000 : ℝ)*X 0 0+(635268307/1250000000 : ℝ)*X 0 1+(5808769173/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((5537846403/10000000000 : ℝ)*X 1 0+(-817845727/5000000000 : ℝ)*X 1 1+(5303679611/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((263451823/625000000 : ℝ)*X 2 0+(671102539/1000000000 : ℝ)*X 2 1+(-1388671077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((7141012889/10000000000 : ℝ)*X 0 0+(2508138787/10000000000 : ℝ)*X 0 1+(2745813117/10000000000 : ℝ)*X 0 2+(7141012889/10000000000 : ℝ)*X 1 0+(2508138787/10000000000 : ℝ)*X 1 1+(2745813117/10000000000 : ℝ)*X 1 2+(7141012889/10000000000 : ℝ)*X 2 0+(2508138787/10000000000 : ℝ)*X 2 1+(2745813117/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309061_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((5439/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5439/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (229827834524834141978890221/27338441750000000000000000000000 : ℝ) := by norm_num
    linear_combination (532050295663/500000000000 : ℝ)*(base59) + (2966039042637/500000000000 : ℝ)*(major_s4_0) + (2966039042637/500000000000 : ℝ)*(major_s4_1) + (2966039042637/500000000000 : ℝ)*(major_s4_2) + (5257487/100000000000 : ℝ)*(sp_s4_0) + (18857129/500000000000 : ℝ)*(sp_s4_1) + (9790187/250000000000 : ℝ)*(sp_s4_6) + (4069510364269/500000000000 : ℝ)*(sp_s4_7) + (8138791373401/1000000000000 : ℝ)*(sp_s4_8) + (813896953821/100000000000 : ℝ)*(sp_s4_9) + (1862520400057/500000000000 : ℝ)*(sp_s4_13) + (104021/1000000000000 : ℝ)*(sp_s4_14) + (24431977/100000000000 : ℝ)*(sp_s4_15) + (103869219/1000000000000 : ℝ)*(sp_s4_23) + (1862539980431/500000000000 : ℝ)*(f.failure) + (8139073407429/1000000000000 : ℝ)*(f.sum) + (52676506816525693/566675525000000000000000000000 : ℝ)*base63 + (183863241547393/296937500000000000000000000 : ℝ)*base64 + (13783442610181/119275000000000000000000000 : ℝ)*base66 + (23828260858431/237550000000000000000000000 : ℝ)*base68 + (20394630448357050193/54676883500000000000000000000000 : ℝ)*base70 + (15927505610173/115085000000000000000000000 : ℝ)*base72 + (27198560466923/238550000000000000000000000 : ℝ)*base74 + (358575160514009/2301700000000000000000000000 : ℝ)*base76 + (490175113084569071/5490705350000000000000000000000 : ℝ)*base79 + (4543/50000000000000000 : ℝ)*base86 + (4543/50000000000000000 : ℝ)*base88 + (4543/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32209/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(32209/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (960611508654758696352185367081/286949752296350000000000000000000000 : ℝ) := by norm_num
    linear_combination (282449/1000000000000 : ℝ)*(base39) + (290617/1000000000000 : ℝ)*(base49) + (665122345427/1000000000000 : ℝ)*(base59) + (285557632179/50000000000 : ℝ)*(major_s4_0) + (285557632179/50000000000 : ℝ)*(major_s4_1) + (285557632179/50000000000 : ℝ)*(major_s4_2) + (532507/62500000000 : ℝ)*(sp_s4_2) + (1439443/200000000000 : ℝ)*(sp_s4_6) + (9530957/500000000000 : ℝ)*(sp_s4_7) + (1958984113439/250000000000 : ℝ)*(sp_s4_14) + (783595551567/100000000000 : ℝ)*(sp_s4_15) + (7835946995557/1000000000000 : ℝ)*(sp_s4_16) + (3586276501717/1000000000000 : ℝ)*(sp_s4_20) + (32478333/500000000000 : ℝ)*(sp_s4_27) + (1793174327799/500000000000 : ℝ)*(f.failure) + (783595551567/100000000000 : ℝ)*(f.sum) + (53498077768545743/1246686155000000000000000000000 : ℝ)*base63 + (30851149562127/237550000000000000000000000 : ℝ)*base65 + (209023152348949/524810000000000000000000000 : ℝ)*base66 + (3166071765467/11877500000000000000000000 : ℝ)*base68 + (667431302078786751/1366922087500000000000000000000 : ℝ)*base71 + (128593128784611/230170000000000000000000000 : ℝ)*base72 + (29401064170977/131202500000000000000000000 : ℝ)*base75 + (57676703662407/230170000000000000000000000 : ℝ)*base77 + (3815330290886131389/12079551770000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (7353/50000000000000000 : ℝ)*base87 + (7353/50000000000000000 : ℝ)*base89 + (7353/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29753/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(29753/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1933641699524841206391/593875000000000000000000000 : ℝ) := by norm_num
    linear_combination (160903504841/500000000000 : ℝ)*(base40) + (168577/200000000000 : ℝ)*(base50) + (669206984031/1000000000000 : ℝ)*(base59) + (5295727723649/1000000000000 : ℝ)*(major_s4_0) + (5295727723649/1000000000000 : ℝ)*(major_s4_1) + (5295727723649/1000000000000 : ℝ)*(major_s4_2) + (540019/500000000000 : ℝ)*(sp_s4_0) + (50330563/500000000000 : ℝ)*(sp_s4_2) + (18551479/1000000000000 : ℝ)*(sp_s4_9) + (258540797/1000000000000 : ℝ)*(sp_s4_20) + (3632986456331/500000000000 : ℝ)*(sp_s4_21) + (72659739927/10000000000 : ℝ)*(sp_s4_22) + (1453170956019/200000000000 : ℝ)*(sp_s4_23) + (3325221828471/1000000000000 : ℝ)*(sp_s4_27) + (3325480369269/1000000000000 : ℝ)*(f.failure) + (72659739927/10000000000 : ℝ)*(f.sum) + (543414392361343897/2266702100000000000000000000000 : ℝ)*base63 + (486564106001431/2375500000000000000000000000 : ℝ)*base65 + (2026981094127/238550000000000000000000000 : ℝ)*base66 + (25694899119/3711718750000000000000000 : ℝ)*base68 + (93454809863839999539/109353767000000000000000000000000 : ℝ)*base71 + (6321293154637/14385625000000000000000000 : ℝ)*base72 + (110218234433731/477100000000000000000000000 : ℝ)*base74 + (664977316232053/4603400000000000000000000000 : ℝ)*base76 + (440200448795243269/1372676337500000000000000000000 : ℝ)*base79 + (80443/100000000000000000 : ℝ)*base87 + (80443/100000000000000000 : ℝ)*base89 + (80443/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((23017/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(23017/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(52481/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(52481/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(4751/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(4751/10000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5439/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5439/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(32209/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(32209/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29753/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(29753/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c309061_s4 p hpa hpb X hX hprev3

#print axioms solution
