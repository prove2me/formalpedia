-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c314063_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:48:28.16051+00:00
-- url     : https://prove2.me/submissions/0942f807-8042-4ed7-ab6e-7aba09551aec

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
theorem collision_support_c314063_s2_s2_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-18781349/156250000 : ℝ)*x 0 + (5454951811/10000000000 : ℝ)*x 1 + (5516893509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (18781349/156250000 : ℝ)^75 ≤ (1691725726989/25000000000000 : ℝ)^59 := by
    have hnat : (18781349 : ℕ)^75*25000000000000^59 ≤ 1691725726989^59*156250000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18781349 156250000 1691725726989 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5454951811/10000000000 : ℝ)^75 ≤ (1446312721091/3125000000000 : ℝ)^59 := by
    have hnat : (5454951811 : ℕ)^75*3125000000000^59 ≤ 1446312721091^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5454951811 10000000000 1446312721091 3125000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5516893509/10000000000 : ℝ)^75 ≤ (23475545003349/50000000000000 : ℝ)^59 := by
    have hnat : (5516893509 : ℕ)^75*50000000000000^59 ≤ 23475545003349^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516893509 10000000000 23475545003349 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-18781349/156250000 : ℝ), (5454951811/10000000000 : ℝ), (5516893509/10000000000 : ℝ)] ![(1691725726989/25000000000000 : ℝ), (1446312721091/3125000000000 : ℝ), (23475545003349/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-18781349/156250000 : ℝ)|^75 ≤ (1691725726989/25000000000000 : ℝ)^59
        have hw : |(-18781349/156250000 : ℝ)|=(18781349/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5454951811/10000000000 : ℝ)|^75 ≤ (1446312721091/3125000000000 : ℝ)^59
        have hw : |(5454951811/10000000000 : ℝ)|=(5454951811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5516893509/10000000000 : ℝ)|^75 ≤ (23475545003349/50000000000000 : ℝ)^59
        have hw : |(5516893509/10000000000 : ℝ)|=(5516893509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s2_s2_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2727629101/5000000000 : ℝ)*x 0 + (-150682671/1250000000 : ℝ)*x 1 + (5514301481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2727629101/5000000000 : ℝ)^75 ≤ (2892831975369/6250000000000 : ℝ)^59 := by
    have hnat : (2727629101 : ℕ)^75*6250000000000^59 ≤ 2892831975369^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727629101 5000000000 2892831975369 6250000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (150682671/1250000000 : ℝ)^75 ≤ (1697909501389/25000000000000 : ℝ)^59 := by
    have hnat : (150682671 : ℕ)^75*25000000000000^59 ≤ 1697909501389^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150682671 1250000000 1697909501389 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5514301481/10000000000 : ℝ)^75 ≤ (5865381296533/12500000000000 : ℝ)^59 := by
    have hnat : (5514301481 : ℕ)^75*12500000000000^59 ≤ 5865381296533^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5514301481 10000000000 5865381296533 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2727629101/5000000000 : ℝ), (-150682671/1250000000 : ℝ), (5514301481/10000000000 : ℝ)] ![(2892831975369/6250000000000 : ℝ), (1697909501389/25000000000000 : ℝ), (5865381296533/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2727629101/5000000000 : ℝ)|^75 ≤ (2892831975369/6250000000000 : ℝ)^59
        have hw : |(2727629101/5000000000 : ℝ)|=(2727629101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-150682671/1250000000 : ℝ)|^75 ≤ (1697909501389/25000000000000 : ℝ)^59
        have hw : |(-150682671/1250000000 : ℝ)|=(150682671/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5514301481/10000000000 : ℝ)|^75 ≤ (5865381296533/12500000000000 : ℝ)^59
        have hw : |(5514301481/10000000000 : ℝ)|=(5514301481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s2_s2_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1372796289/2500000000 : ℝ)*x 0 + (5504604729/10000000000 : ℝ)*x 1 + (-582886347/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1372796289/2500000000 : ℝ)^75 ≤ (4667314442481/10000000000000 : ℝ)^59 := by
    have hnat : (1372796289 : ℕ)^75*10000000000000^59 ≤ 4667314442481^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372796289 2500000000 4667314442481 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5504604729/10000000000 : ℝ)^75 ≤ (46818186072253/100000000000000 : ℝ)^59 := by
    have hnat : (5504604729 : ℕ)^75*100000000000000^59 ≤ 46818186072253^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504604729 10000000000 46818186072253 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (582886347/5000000000 : ℝ)^75 ≤ (6508669488417/100000000000000 : ℝ)^59 := by
    have hnat : (582886347 : ℕ)^75*100000000000000^59 ≤ 6508669488417^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      582886347 5000000000 6508669488417 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1372796289/2500000000 : ℝ), (5504604729/10000000000 : ℝ), (-582886347/5000000000 : ℝ)] ![(4667314442481/10000000000000 : ℝ), (46818186072253/100000000000000 : ℝ), (6508669488417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1372796289/2500000000 : ℝ)|^75 ≤ (4667314442481/10000000000000 : ℝ)^59
        have hw : |(1372796289/2500000000 : ℝ)|=(1372796289/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5504604729/10000000000 : ℝ)|^75 ≤ (46818186072253/100000000000000 : ℝ)^59
        have hw : |(5504604729/10000000000 : ℝ)|=(5504604729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-582886347/5000000000 : ℝ)|^75 ≤ (6508669488417/100000000000000 : ℝ)^59
        have hw : |(-582886347/5000000000 : ℝ)|=(582886347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s2_s2_6 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (853493283/2000000000 : ℝ)*x 0 + (4226352227/10000000000 : ℝ)*x 1 + (4147069183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (853493283/2000000000 : ℝ)^75 ≤ (33874840646673/100000000000000 : ℝ)^59 := by
    have hnat : (853493283 : ℕ)^75*100000000000000^59 ≤ 33874840646673^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853493283 2000000000 33874840646673 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4226352227/10000000000 : ℝ)^75 ≤ (4182564702399/12500000000000 : ℝ)^59 := by
    have hnat : (4226352227 : ℕ)^75*12500000000000^59 ≤ 4182564702399^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226352227 10000000000 4182564702399 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4147069183/10000000000 : ℝ)^75 ≤ (6532928342631/20000000000000 : ℝ)^59 := by
    have hnat : (4147069183 : ℕ)^75*20000000000000^59 ≤ 6532928342631^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4147069183 10000000000 6532928342631 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(853493283/2000000000 : ℝ), (4226352227/10000000000 : ℝ), (4147069183/10000000000 : ℝ)] ![(33874840646673/100000000000000 : ℝ), (4182564702399/12500000000000 : ℝ), (6532928342631/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(853493283/2000000000 : ℝ)|^75 ≤ (33874840646673/100000000000000 : ℝ)^59
        have hw : |(853493283/2000000000 : ℝ)|=(853493283/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4226352227/10000000000 : ℝ)|^75 ≤ (4182564702399/12500000000000 : ℝ)^59
        have hw : |(4226352227/10000000000 : ℝ)|=(4226352227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4147069183/10000000000 : ℝ)|^75 ≤ (6532928342631/20000000000000 : ℝ)^59
        have hw : |(4147069183/10000000000 : ℝ)|=(4147069183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s2_s2_7 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1001156707/10000000000 : ℝ)*x 0 + (226367351/500000000 : ℝ)*x 1 + (10440243/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1001156707/10000000000 : ℝ)^75 ≤ (5363543072917/100000000000000 : ℝ)^59 := by
    have hnat : (1001156707 : ℕ)^75*100000000000000^59 ≤ 5363543072917^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1001156707 10000000000 5363543072917 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226367351/500000000 : ℝ)^75 ≤ (36518529818697/100000000000000 : ℝ)^59 := by
    have hnat : (226367351 : ℕ)^75*100000000000000^59 ≤ 36518529818697^59*500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226367351 500000000 36518529818697 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10440243/16000000 : ℝ)^75 ≤ (29058963549411/50000000000000 : ℝ)^59 := by
    have hnat : (10440243 : ℕ)^75*50000000000000^59 ≤ 29058963549411^59*16000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10440243 16000000 29058963549411 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1001156707/10000000000 : ℝ), (226367351/500000000 : ℝ), (10440243/16000000 : ℝ)] ![(5363543072917/100000000000000 : ℝ), (36518529818697/100000000000000 : ℝ), (29058963549411/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1001156707/10000000000 : ℝ)|^75 ≤ (5363543072917/100000000000000 : ℝ)^59
        have hw : |(-1001156707/10000000000 : ℝ)|=(1001156707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(226367351/500000000 : ℝ)|^75 ≤ (36518529818697/100000000000000 : ℝ)^59
        have hw : |(226367351/500000000 : ℝ)|=(226367351/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10440243/16000000 : ℝ)|^75 ≤ (29058963549411/50000000000000 : ℝ)^59
        have hw : |(10440243/16000000 : ℝ)|=(10440243/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s2_s2_8 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (615160787/1250000000 : ℝ)*x 0 + (-329784557/10000000000 : ℝ)*x 1 + (6522518049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (615160787/1250000000 : ℝ)^75 ≤ (40604534010203/100000000000000 : ℝ)^59 := by
    have hnat : (615160787 : ℕ)^75*100000000000000^59 ≤ 40604534010203^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      615160787 1250000000 40604534010203 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (329784557/10000000000 : ℝ)^75 ≤ (1307357817121/100000000000000 : ℝ)^59 := by
    have hnat : (329784557 : ℕ)^75*100000000000000^59 ≤ 1307357817121^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329784557 10000000000 1307357817121 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6522518049/10000000000 : ℝ)^75 ≤ (11617621633823/20000000000000 : ℝ)^59 := by
    have hnat : (6522518049 : ℕ)^75*20000000000000^59 ≤ 11617621633823^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6522518049 10000000000 11617621633823 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(615160787/1250000000 : ℝ), (-329784557/10000000000 : ℝ), (6522518049/10000000000 : ℝ)] ![(40604534010203/100000000000000 : ℝ), (1307357817121/100000000000000 : ℝ), (11617621633823/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(615160787/1250000000 : ℝ)|^75 ≤ (40604534010203/100000000000000 : ℝ)^59
        have hw : |(615160787/1250000000 : ℝ)|=(615160787/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-329784557/10000000000 : ℝ)|^75 ≤ (1307357817121/100000000000000 : ℝ)^59
        have hw : |(-329784557/10000000000 : ℝ)|=(329784557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6522518049/10000000000 : ℝ)|^75 ≤ (11617621633823/20000000000000 : ℝ)^59
        have hw : |(6522518049/10000000000 : ℝ)|=(6522518049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s2_s2_9 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1164803379/2500000000 : ℝ)*x 0 + (848641377/1250000000 : ℝ)*x 1 + (-267322367/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1164803379/2500000000 : ℝ)^75 ≤ (18937973112979/50000000000000 : ℝ)^59 := by
    have hnat : (1164803379 : ℕ)^75*50000000000000^59 ≤ 18937973112979^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1164803379 2500000000 18937973112979 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (848641377/1250000000 : ℝ)^75 ≤ (30561487095027/50000000000000 : ℝ)^59 := by
    have hnat : (848641377 : ℕ)^75*50000000000000^59 ≤ 30561487095027^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848641377 1250000000 30561487095027 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (267322367/10000000000 : ℝ)^75 ≤ (1001079571507/100000000000000 : ℝ)^59 := by
    have hnat : (267322367 : ℕ)^75*100000000000000^59 ≤ 1001079571507^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267322367 10000000000 1001079571507 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1164803379/2500000000 : ℝ), (848641377/1250000000 : ℝ), (-267322367/10000000000 : ℝ)] ![(18937973112979/50000000000000 : ℝ), (30561487095027/50000000000000 : ℝ), (1001079571507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1164803379/2500000000 : ℝ)|^75 ≤ (18937973112979/50000000000000 : ℝ)^59
        have hw : |(1164803379/2500000000 : ℝ)|=(1164803379/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(848641377/1250000000 : ℝ)|^75 ≤ (30561487095027/50000000000000 : ℝ)^59
        have hw : |(848641377/1250000000 : ℝ)|=(848641377/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-267322367/10000000000 : ℝ)|^75 ≤ (1001079571507/100000000000000 : ℝ)^59
        have hw : |(-267322367/10000000000 : ℝ)|=(267322367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s2_s2_13 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1114467197/2500000000 : ℝ)*x 0 + (5980849551/10000000000 : ℝ)*x 1 + (238355519/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1114467197/2500000000 : ℝ)^75 ≤ (35807611893863/100000000000000 : ℝ)^59 := by
    have hnat : (1114467197 : ℕ)^75*100000000000000^59 ≤ 35807611893863^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114467197 2500000000 35807611893863 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5980849551/10000000000 : ℝ)^75 ≤ (52026426543739/100000000000000 : ℝ)^59 := by
    have hnat : (5980849551 : ℕ)^75*100000000000000^59 ≤ 52026426543739^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5980849551 10000000000 52026426543739 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (238355519/1250000000 : ℝ)^75 ≤ (47523287321/390625000000 : ℝ)^59 := by
    have hnat : (238355519 : ℕ)^75*390625000000^59 ≤ 47523287321^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238355519 1250000000 47523287321 390625000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1114467197/2500000000 : ℝ), (5980849551/10000000000 : ℝ), (238355519/1250000000 : ℝ)] ![(35807611893863/100000000000000 : ℝ), (52026426543739/100000000000000 : ℝ), (47523287321/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1114467197/2500000000 : ℝ)|^75 ≤ (35807611893863/100000000000000 : ℝ)^59
        have hw : |(1114467197/2500000000 : ℝ)|=(1114467197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5980849551/10000000000 : ℝ)|^75 ≤ (52026426543739/100000000000000 : ℝ)^59
        have hw : |(5980849551/10000000000 : ℝ)|=(5980849551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(238355519/1250000000 : ℝ)|^75 ≤ (47523287321/390625000000 : ℝ)^59
        have hw : |(238355519/1250000000 : ℝ)|=(238355519/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s2_s2_14 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-31986279/1000000000 : ℝ)*x 0 + (4936536423/10000000000 : ℝ)*x 1 + (325638999/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31986279/1000000000 : ℝ)^75 ≤ (628782083191/50000000000000 : ℝ)^59 := by
    have hnat : (31986279 : ℕ)^75*50000000000000^59 ≤ 628782083191^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31986279 1000000000 628782083191 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4936536423/10000000000 : ℝ)^75 ≤ (40764549091821/100000000000000 : ℝ)^59 := by
    have hnat : (4936536423 : ℕ)^75*100000000000000^59 ≤ 40764549091821^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4936536423 10000000000 40764549091821 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (325638999/500000000 : ℝ)^75 ≤ (28988943364267/50000000000000 : ℝ)^59 := by
    have hnat : (325638999 : ℕ)^75*50000000000000^59 ≤ 28988943364267^59*500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325638999 500000000 28988943364267 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-31986279/1000000000 : ℝ), (4936536423/10000000000 : ℝ), (325638999/500000000 : ℝ)] ![(628782083191/50000000000000 : ℝ), (40764549091821/100000000000000 : ℝ), (28988943364267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-31986279/1000000000 : ℝ)|^75 ≤ (628782083191/50000000000000 : ℝ)^59
        have hw : |(-31986279/1000000000 : ℝ)|=(31986279/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4936536423/10000000000 : ℝ)|^75 ≤ (40764549091821/100000000000000 : ℝ)^59
        have hw : |(4936536423/10000000000 : ℝ)|=(4936536423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(325638999/500000000 : ℝ)|^75 ≤ (28988943364267/50000000000000 : ℝ)^59
        have hw : |(325638999/500000000 : ℝ)|=(325638999/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s2_s2_15 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4554899159/10000000000 : ℝ)*x 0 + (-492271191/5000000000 : ℝ)*x 1 + (6510145449/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4554899159/10000000000 : ℝ)^75 ≤ (36801272758591/100000000000000 : ℝ)^59 := by
    have hnat : (4554899159 : ℕ)^75*100000000000000^59 ≤ 36801272758591^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4554899159 10000000000 36801272758591 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (492271191/5000000000 : ℝ)^75 ≤ (5250652067061/100000000000000 : ℝ)^59 := by
    have hnat : (492271191 : ℕ)^75*100000000000000^59 ≤ 5250652067061^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492271191 5000000000 5250652067061 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6510145449/10000000000 : ℝ)^75 ≤ (57948075167641/100000000000000 : ℝ)^59 := by
    have hnat : (6510145449 : ℕ)^75*100000000000000^59 ≤ 57948075167641^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6510145449 10000000000 57948075167641 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4554899159/10000000000 : ℝ), (-492271191/5000000000 : ℝ), (6510145449/10000000000 : ℝ)] ![(36801272758591/100000000000000 : ℝ), (5250652067061/100000000000000 : ℝ), (57948075167641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4554899159/10000000000 : ℝ)|^75 ≤ (36801272758591/100000000000000 : ℝ)^59
        have hw : |(4554899159/10000000000 : ℝ)|=(4554899159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-492271191/5000000000 : ℝ)|^75 ≤ (5250652067061/100000000000000 : ℝ)^59
        have hw : |(-492271191/5000000000 : ℝ)|=(492271191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6510145449/10000000000 : ℝ)|^75 ≤ (57948075167641/100000000000000 : ℝ)^59
        have hw : |(6510145449/10000000000 : ℝ)|=(6510145449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s2_s2_16 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (648331003/1000000000 : ℝ)*x 0 + (4987005197/10000000000 : ℝ)*x 1 + (-279694673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (648331003/1000000000 : ℝ)^75 ≤ (7205575022293/12500000000000 : ℝ)^59 := by
    have hnat : (648331003 : ℕ)^75*12500000000000^59 ≤ 7205575022293^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648331003 1000000000 7205575022293 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4987005197/10000000000 : ℝ)^75 ≤ (8259011540311/20000000000000 : ℝ)^59 := by
    have hnat : (4987005197 : ℕ)^75*20000000000000^59 ≤ 8259011540311^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4987005197 10000000000 8259011540311 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (279694673/10000000000 : ℝ)^75 ≤ (530171056733/50000000000000 : ℝ)^59 := by
    have hnat : (279694673 : ℕ)^75*50000000000000^59 ≤ 530171056733^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279694673 10000000000 530171056733 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(648331003/1000000000 : ℝ), (4987005197/10000000000 : ℝ), (-279694673/10000000000 : ℝ)] ![(7205575022293/12500000000000 : ℝ), (8259011540311/20000000000000 : ℝ), (530171056733/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(648331003/1000000000 : ℝ)|^75 ≤ (7205575022293/12500000000000 : ℝ)^59
        have hw : |(648331003/1000000000 : ℝ)|=(648331003/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4987005197/10000000000 : ℝ)|^75 ≤ (8259011540311/20000000000000 : ℝ)^59
        have hw : |(4987005197/10000000000 : ℝ)|=(4987005197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-279694673/10000000000 : ℝ)|^75 ≤ (530171056733/50000000000000 : ℝ)^59
        have hw : |(-279694673/10000000000 : ℝ)|=(279694673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s2_s2_20 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (167110749/250000000 : ℝ)*x 0 + (1819323217/5000000000 : ℝ)*x 1 + (1937049503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167110749/250000000 : ℝ)^75 ≤ (59927230588087/100000000000000 : ℝ)^59 := by
    have hnat : (167110749 : ℕ)^75*100000000000000^59 ≤ 59927230588087^59*250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167110749 250000000 59927230588087 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1819323217/5000000000 : ℝ)^75 ≤ (1728831700849/6250000000000 : ℝ)^59 := by
    have hnat : (1819323217 : ℕ)^75*6250000000000^59 ≤ 1728831700849^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1819323217 5000000000 1728831700849 6250000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1937049503/10000000000 : ℝ)^75 ≤ (12411462192821/100000000000000 : ℝ)^59 := by
    have hnat : (1937049503 : ℕ)^75*100000000000000^59 ≤ 12411462192821^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1937049503 10000000000 12411462192821 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167110749/250000000 : ℝ), (1819323217/5000000000 : ℝ), (1937049503/10000000000 : ℝ)] ![(59927230588087/100000000000000 : ℝ), (1728831700849/6250000000000 : ℝ), (12411462192821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167110749/250000000 : ℝ)|^75 ≤ (59927230588087/100000000000000 : ℝ)^59
        have hw : |(167110749/250000000 : ℝ)|=(167110749/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1819323217/5000000000 : ℝ)|^75 ≤ (1728831700849/6250000000000 : ℝ)^59
        have hw : |(1819323217/5000000000 : ℝ)|=(1819323217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1937049503/10000000000 : ℝ)|^75 ≤ (12411462192821/100000000000000 : ℝ)^59
        have hw : |(1937049503/10000000000 : ℝ)|=(1937049503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s2_s2_21 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-33099109/1250000000 : ℝ)*x 0 + (3060600033/5000000000 : ℝ)*x 1 + (2687789023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (33099109/1250000000 : ℝ)^75 ≤ (61815854587/6250000000000 : ℝ)^59 := by
    have hnat : (33099109 : ℕ)^75*6250000000000^59 ≤ 61815854587^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33099109 1250000000 61815854587 6250000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3060600033/5000000000 : ℝ)^75 ≤ (53583310714803/100000000000000 : ℝ)^59 := by
    have hnat : (3060600033 : ℕ)^75*100000000000000^59 ≤ 53583310714803^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3060600033 5000000000 53583310714803 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687789023/5000000000 : ℝ)^75 ≤ (567845444971/1250000000000 : ℝ)^59 := by
    have hnat : (2687789023 : ℕ)^75*1250000000000^59 ≤ 567845444971^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687789023 5000000000 567845444971 1250000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-33099109/1250000000 : ℝ), (3060600033/5000000000 : ℝ), (2687789023/5000000000 : ℝ)] ![(61815854587/6250000000000 : ℝ), (53583310714803/100000000000000 : ℝ), (567845444971/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-33099109/1250000000 : ℝ)|^75 ≤ (61815854587/6250000000000 : ℝ)^59
        have hw : |(-33099109/1250000000 : ℝ)|=(33099109/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3060600033/5000000000 : ℝ)|^75 ≤ (53583310714803/100000000000000 : ℝ)^59
        have hw : |(3060600033/5000000000 : ℝ)|=(3060600033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687789023/5000000000 : ℝ)|^75 ≤ (567845444971/1250000000000 : ℝ)^59
        have hw : |(2687789023/5000000000 : ℝ)|=(2687789023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s2_s2_22 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6501862743/10000000000 : ℝ)*x 0 + (-6356931/250000000 : ℝ)*x 1 + (4978564697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6501862743/10000000000 : ℝ)^75 ≤ (57854371871017/100000000000000 : ℝ)^59 := by
    have hnat : (6501862743 : ℕ)^75*100000000000000^59 ≤ 57854371871017^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6501862743 10000000000 57854371871017 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6356931/250000000 : ℝ)^75 ≤ (187879111809/20000000000000 : ℝ)^59 := by
    have hnat : (6356931 : ℕ)^75*20000000000000^59 ≤ 187879111809^59*250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6356931 250000000 187879111809 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4978564697/10000000000 : ℝ)^75 ≤ (41206232548773/100000000000000 : ℝ)^59 := by
    have hnat : (4978564697 : ℕ)^75*100000000000000^59 ≤ 41206232548773^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4978564697 10000000000 41206232548773 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6501862743/10000000000 : ℝ), (-6356931/250000000 : ℝ), (4978564697/10000000000 : ℝ)] ![(57854371871017/100000000000000 : ℝ), (187879111809/20000000000000 : ℝ), (41206232548773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6501862743/10000000000 : ℝ)|^75 ≤ (57854371871017/100000000000000 : ℝ)^59
        have hw : |(6501862743/10000000000 : ℝ)|=(6501862743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6356931/250000000 : ℝ)|^75 ≤ (187879111809/20000000000000 : ℝ)^59
        have hw : |(-6356931/250000000 : ℝ)|=(6356931/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4978564697/10000000000 : ℝ)|^75 ≤ (41206232548773/100000000000000 : ℝ)^59
        have hw : |(4978564697/10000000000 : ℝ)|=(4978564697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s2_s2_23 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1129661483/2500000000 : ℝ)*x 0 + (1313209511/2000000000 : ℝ)*x 1 + (-472892477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1129661483/2500000000 : ℝ)^75 ≤ (36429335114301/100000000000000 : ℝ)^59 := by
    have hnat : (1129661483 : ℕ)^75*100000000000000^59 ≤ 36429335114301^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1129661483 2500000000 36429335114301 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1313209511/2000000000 : ℝ)^75 ≤ (58581346840343/100000000000000 : ℝ)^59 := by
    have hnat : (1313209511 : ℕ)^75*100000000000000^59 ≤ 58581346840343^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313209511 2000000000 58581346840343 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (472892477/5000000000 : ℝ)^75 ≤ (4989318026799/100000000000000 : ℝ)^59 := by
    have hnat : (472892477 : ℕ)^75*100000000000000^59 ≤ 4989318026799^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472892477 5000000000 4989318026799 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1129661483/2500000000 : ℝ), (1313209511/2000000000 : ℝ), (-472892477/5000000000 : ℝ)] ![(36429335114301/100000000000000 : ℝ), (58581346840343/100000000000000 : ℝ), (4989318026799/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1129661483/2500000000 : ℝ)|^75 ≤ (36429335114301/100000000000000 : ℝ)^59
        have hw : |(1129661483/2500000000 : ℝ)|=(1129661483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1313209511/2000000000 : ℝ)|^75 ≤ (58581346840343/100000000000000 : ℝ)^59
        have hw : |(1313209511/2000000000 : ℝ)|=(1313209511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-472892477/5000000000 : ℝ)|^75 ≤ (4989318026799/100000000000000 : ℝ)^59
        have hw : |(-472892477/5000000000 : ℝ)|=(472892477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314063_s2_s2_27 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3431045329/5000000000 : ℝ)*x 0 + (281861993/1000000000 : ℝ)*x 1 + (2600400713/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3431045329/5000000000 : ℝ)^75 ≤ (30979589794727/50000000000000 : ℝ)^59 := by
    have hnat : (3431045329 : ℕ)^75*50000000000000^59 ≤ 30979589794727^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3431045329 5000000000 30979589794727 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281861993/1000000000 : ℝ)^75 ≤ (19993732594689/100000000000000 : ℝ)^59 := by
    have hnat : (281861993 : ℕ)^75*100000000000000^59 ≤ 19993732594689^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281861993 1000000000 19993732594689 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2600400713/10000000000 : ℝ)^75 ≤ (563971493583/3125000000000 : ℝ)^59 := by
    have hnat : (2600400713 : ℕ)^75*3125000000000^59 ≤ 563971493583^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2600400713 10000000000 563971493583 3125000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3431045329/5000000000 : ℝ), (281861993/1000000000 : ℝ), (2600400713/10000000000 : ℝ)] ![(30979589794727/50000000000000 : ℝ), (19993732594689/100000000000000 : ℝ), (563971493583/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3431045329/5000000000 : ℝ)|^75 ≤ (30979589794727/50000000000000 : ℝ)^59
        have hw : |(3431045329/5000000000 : ℝ)|=(3431045329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281861993/1000000000 : ℝ)|^75 ≤ (19993732594689/100000000000000 : ℝ)^59
        have hw : |(281861993/1000000000 : ℝ)|=(281861993/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2600400713/10000000000 : ℝ)|^75 ≤ (563971493583/3125000000000 : ℝ)^59
        have hw : |(2600400713/10000000000 : ℝ)|=(2600400713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314063_s2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((63337/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(63337/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(63549/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(63549/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61031/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61031/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((44137/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(44137/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8973/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8973/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10713/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(10713/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15771/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15771/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.2.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (63337/100000 : ℝ) ^ (37/8 : ℝ) ≤ (12096671472621220543/100000000000000000000 : ℝ) := by
    have hpowers : (63337/100000 : ℝ)^37 ≤ (12096671472621220543/100000000000000000000 : ℝ)^8 := by
      have hnat : (63337 : ℕ)^37*100000000000000000000^8 ≤ 12096671472621220543^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63337 100000 12096671472621220543 100000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (63337/100000 : ℝ)) (X := (12096671472621220543/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner0a : (112096671472621220543/100000000000000000000 : ℝ) ≤ (2049994733361923/2000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (112096671472621220543/100000000000000000000 : ℝ)^8 ≤ (2049994733361923/2000000000000000 : ℝ)^37 := by
      have hnat : (112096671472621220543 : ℕ)^8*2000000000000000^37 ≤ 2049994733361923^37*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        112096671472621220543 100000000000000000000 2049994733361923 2000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2049994733361923/2000000000000000 : ℝ)) (X := (112096671472621220543/100000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner0b : (62096671472621220543/50000000000000000000 : ℝ) ≤ (10479621135741681/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (62096671472621220543/50000000000000000000 : ℝ)^8 ≤ (10479621135741681/10000000000000000 : ℝ)^37 := by
      have hnat : (62096671472621220543 : ℕ)^8*10000000000000000^37 ≤ 10479621135741681^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62096671472621220543 50000000000000000000 10479621135741681 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10479621135741681/10000000000000000 : ℝ)) (X := (62096671472621220543/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(49994733361923/1266740000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(114823734466033/3166850000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (63337/100000 : ℝ)) (alpha := (49994733361923/1266740000000000 : ℝ)) (beta := (114823734466033/3166850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (63337/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(49994733361923/1266740000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(114823734466033/3166850000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (63549/100000 : ℝ) ^ (37/8 : ℝ) ≤ (6142537813166789467/50000000000000000000 : ℝ) := by
    have hpowers : (63549/100000 : ℝ)^37 ≤ (6142537813166789467/50000000000000000000 : ℝ)^8 := by
      have hnat : (63549 : ℕ)^37*50000000000000000000^8 ≤ 6142537813166789467^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63549 100000 6142537813166789467 50000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (63549/100000 : ℝ)) (X := (6142537813166789467/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner1a : (56142537813166789467/50000000000000000000 : ℝ) ≤ (2563424016416479/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (56142537813166789467/50000000000000000000 : ℝ)^8 ≤ (2563424016416479/2500000000000000 : ℝ)^37 := by
      have hnat : (56142537813166789467 : ℕ)^8*2500000000000000^37 ≤ 2563424016416479^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56142537813166789467 50000000000000000000 2563424016416479 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2563424016416479/2500000000000000 : ℝ)) (X := (56142537813166789467/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner1b : (31142537813166789467/25000000000000000000 : ℝ) ≤ (5243243855911107/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (31142537813166789467/25000000000000000000 : ℝ)^8 ≤ (5243243855911107/5000000000000000 : ℝ)^37 := by
      have hnat : (31142537813166789467 : ℕ)^8*5000000000000000^37 ≤ 5243243855911107^37*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31142537813166789467 25000000000000000000 5243243855911107 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5243243855911107/5000000000000000 : ℝ)) (X := (31142537813166789467/25000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(21141338805493/529575000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(116395823078149/3177450000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (63549/100000 : ℝ)) (alpha := (21141338805493/529575000000000 : ℝ)) (beta := (116395823078149/3177450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (63549/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(21141338805493/529575000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(116395823078149/3177450000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (61031/100000 : ℝ) ^ (37/8 : ℝ) ≤ (2037985047581339573/20000000000000000000 : ℝ) := by
    have hpowers : (61031/100000 : ℝ)^37 ≤ (2037985047581339573/20000000000000000000 : ℝ)^8 := by
      have hnat : (61031 : ℕ)^37*20000000000000000000^8 ≤ 2037985047581339573^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61031 100000 2037985047581339573 20000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (61031/100000 : ℝ)) (X := (2037985047581339573/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner2a : (22037985047581339573/20000000000000000000 : ℝ) ≤ (1276502802644079/1250000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (22037985047581339573/20000000000000000000 : ℝ)^8 ≤ (1276502802644079/1250000000000000 : ℝ)^37 := by
      have hnat : (22037985047581339573 : ℕ)^8*1250000000000000^37 ≤ 1276502802644079^37*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22037985047581339573 20000000000000000000 1276502802644079 1250000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1276502802644079/1250000000000000 : ℝ)) (X := (22037985047581339573/20000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s2_corner2b : (12037985047581339573/10000000000000000000 : ℝ) ≤ (10409192442605723/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (12037985047581339573/10000000000000000000 : ℝ)^8 ≤ (10409192442605723/10000000000000000 : ℝ)^37 := by
      have hnat : (12037985047581339573 : ℕ)^8*10000000000000000^37 ≤ 10409192442605723^37*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12037985047581339573 10000000000000000000 10409192442605723 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10409192442605723/10000000000000000 : ℝ)) (X := (12037985047581339573/10000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(26502802644079/762887500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(197170021453091/6103100000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (61031/100000 : ℝ)) (alpha := (26502802644079/762887500000000 : ℝ)) (beta := (197170021453091/6103100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (61031/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(26502802644079/762887500000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(197170021453091/6103100000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-18781349/156250000 : ℝ)*X 0 0+(5454951811/10000000000 : ℝ)*X 0 1+(5516893509/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((2727629101/5000000000 : ℝ)*X 1 0+(-150682671/1250000000 : ℝ)*X 1 1+(5514301481/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((1372796289/2500000000 : ℝ)*X 2 0+(5504604729/10000000000 : ℝ)*X 2 1+(-582886347/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((853493283/2000000000 : ℝ)*X 0 0+(4226352227/10000000000 : ℝ)*X 0 1+(4147069183/10000000000 : ℝ)*X 0 2+(853493283/2000000000 : ℝ)*X 1 0+(4226352227/10000000000 : ℝ)*X 1 1+(4147069183/10000000000 : ℝ)*X 1 2+(853493283/2000000000 : ℝ)*X 2 0+(4226352227/10000000000 : ℝ)*X 2 1+(4147069183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1001156707/10000000000 : ℝ)*X 0 0+(226367351/500000000 : ℝ)*X 0 1+(10440243/16000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((615160787/1250000000 : ℝ)*X 1 0+(-329784557/10000000000 : ℝ)*X 1 1+(6522518049/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((1164803379/2500000000 : ℝ)*X 2 0+(848641377/1250000000 : ℝ)*X 2 1+(-267322367/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((1114467197/2500000000 : ℝ)*X 0 0+(5980849551/10000000000 : ℝ)*X 0 1+(238355519/1250000000 : ℝ)*X 0 2+(1114467197/2500000000 : ℝ)*X 1 0+(5980849551/10000000000 : ℝ)*X 1 1+(238355519/1250000000 : ℝ)*X 1 2+(1114467197/2500000000 : ℝ)*X 2 0+(5980849551/10000000000 : ℝ)*X 2 1+(238355519/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-31986279/1000000000 : ℝ)*X 0 0+(4936536423/10000000000 : ℝ)*X 0 1+(325638999/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((4554899159/10000000000 : ℝ)*X 1 0+(-492271191/5000000000 : ℝ)*X 1 1+(6510145449/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((648331003/1000000000 : ℝ)*X 2 0+(4987005197/10000000000 : ℝ)*X 2 1+(-279694673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((167110749/250000000 : ℝ)*X 0 0+(1819323217/5000000000 : ℝ)*X 0 1+(1937049503/10000000000 : ℝ)*X 0 2+(167110749/250000000 : ℝ)*X 1 0+(1819323217/5000000000 : ℝ)*X 1 1+(1937049503/10000000000 : ℝ)*X 1 2+(167110749/250000000 : ℝ)*X 2 0+(1819323217/5000000000 : ℝ)*X 2 1+(1937049503/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-33099109/1250000000 : ℝ)*X 0 0+(3060600033/5000000000 : ℝ)*X 0 1+(2687789023/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((6501862743/10000000000 : ℝ)*X 1 0+(-6356931/250000000 : ℝ)*X 1 1+(4978564697/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((1129661483/2500000000 : ℝ)*X 2 0+(1313209511/2000000000 : ℝ)*X 2 1+(-472892477/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((3431045329/5000000000 : ℝ)*X 0 0+(281861993/1000000000 : ℝ)*X 0 1+(2600400713/10000000000 : ℝ)*X 0 2+(3431045329/5000000000 : ℝ)*X 1 0+(281861993/1000000000 : ℝ)*X 1 1+(2600400713/10000000000 : ℝ)*X 1 2+(3431045329/5000000000 : ℝ)*X 2 0+(281861993/1000000000 : ℝ)*X 2 1+(2600400713/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314063_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((44137/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(44137/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (12108433116432217944253455174581/2047082990720025000000000000000000000 : ℝ) := by norm_num
    linear_combination (2723327/1000000000000 : ℝ)*(base23) + (393073/1000000000000 : ℝ)*(base50) + (39027104691/250000000000 : ℝ)*(base60) + (3684813017299/1000000000000 : ℝ)*(major_s2_0) + (3684813017299/1000000000000 : ℝ)*(major_s2_1) + (3684813017299/1000000000000 : ℝ)*(major_s2_2) + (4917301/1000000000000 : ℝ)*(sp_s2_6) + (1307033498997/250000000000 : ℝ)*(sp_s2_7) + (5228123787671/1000000000000 : ℝ)*(sp_s2_8) + (5228123068363/1000000000000 : ℝ)*(sp_s2_9) + (1070734576289/500000000000 : ℝ)*(sp_s2_13) + (15997069/1000000000000 : ℝ)*(sp_s2_14) + (13102693/500000000000 : ℝ)*(sp_s2_15) + (24201367/1000000000000 : ℝ)*(sp_s2_23) + (2141474069879/1000000000000 : ℝ)*(f.failure) + (5228149993057/1000000000000 : ℝ)*(f.sum) + (15008478172048449961/64640983650000000000000000000000 : ℝ)*base63 + (4925059484941911/6103100000000000000000000000 : ℝ)*base64 + (600722994505601/794362500000000000000000000 : ℝ)*base66 + (1194174099151711/3051550000000000000000000000 : ℝ)*base68 + (24146295830720566619/48319005587500000000000000000000 : ℝ)*base70 + (1424172975282553/3166850000000000000000000000 : ℝ)*base72 + (266258527537051/1059150000000000000000000000 : ℝ)*base74 + (1323711313227/2026784000000000000000000 : ℝ)*base76 + (8408375399130209933/20125015065000000000000000000000 : ℝ)*base78 + (109651/100000000000000000 : ℝ)*base87 + (109651/100000000000000000 : ℝ)*base89 + (109651/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8973/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8973/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2793400953255453417581894452981/170590249226668750000000000000000000 : ℝ) := by norm_num
    linear_combination (9194527/1000000000000 : ℝ)*(base21) + (20863/1000000000000 : ℝ)*(base39) + (330367/1000000000000 : ℝ)*(base60) + (465674197147/125000000000 : ℝ)*(major_s2_0) + (465674197147/125000000000 : ℝ)*(major_s2_1) + (465674197147/125000000000 : ℝ)*(major_s2_2) + (21765469/500000000000 : ℝ)*(sp_s2_2) + (16543391/250000000000 : ℝ)*(sp_s2_7) + (2598139/50000000000 : ℝ)*(sp_s2_8) + (5285657564811/1000000000000 : ℝ)*(sp_s2_14) + (1057134355119/200000000000 : ℝ)*(sp_s2_15) + (528567101291/100000000000 : ℝ)*(sp_s2_16) + (17320044153/8000000000 : ℝ)*(sp_s2_20) + (2621927/50000000000 : ℝ)*(sp_s2_27) + (1082528978833/500000000000 : ℝ)*(f.failure) + (42285789907/8000000000 : ℝ)*(f.sum) + (15301333364422891207/32320491825000000000000000000000 : ℝ)*base63 + (1668066361179143/3051550000000000000000000000 : ℝ)*base65 + (1834500626321849/3177450000000000000000000000 : ℝ)*base67 + (2720076046308841/3051550000000000000000000000 : ℝ)*base69 + (5909011790634844479/48319005587500000000000000000000 : ℝ)*base71 + (181633346756429/1583425000000000000000000000 : ℝ)*base73 + (220680451985779/264787500000000000000000000 : ℝ)*base75 + (38631940728581/63337000000000000000000000 : ℝ)*base77 + (11360973069355514993/40250030130000000000000000000000 : ℝ)*base78 + (15477/50000000000000000 : ℝ)*base87 + (15477/50000000000000000 : ℝ)*base89 + (15477/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10713/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(10713/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (783927185211230633316116127/193276022350000000000000000000000 : ℝ) := by norm_num
    linear_combination (1263199/500000000000 : ℝ)*(base15) + (97631858149/500000000000 : ℝ)*(base40) + (3489586458101/1000000000000 : ℝ)*(major_s2_0) + (3489586458101/1000000000000 : ℝ)*(major_s2_1) + (3489586458101/1000000000000 : ℝ)*(major_s2_2) + (2274461/125000000000 : ℝ)*(sp_s2_0) + (16062409/1000000000000 : ℝ)*(sp_s2_1) + (258151/31250000000 : ℝ)*(sp_s2_2) + (16061949/1000000000000 : ℝ)*(sp_s2_9) + (24855043/1000000000000 : ℝ)*(sp_s2_20) + (4951137596873/1000000000000 : ℝ)*(sp_s2_21) + (2475568601877/500000000000 : ℝ)*(sp_s2_22) + (247556573489/50000000000 : ℝ)*(sp_s2_23) + (506997729149/250000000000 : ℝ)*(sp_s2_27) + (2028015771639/1000000000000 : ℝ)*(f.failure) + (4951155792561/1000000000000 : ℝ)*(f.sum) + (9064267143847040483/32320491825000000000000000000000 : ℝ)*base62 + (1164238141406511/6103100000000000000000000000 : ℝ)*base65 + (401362677330217/1588725000000000000000000000 : ℝ)*base67 + (74996154845319/762887500000000000000000000 : ℝ)*base69 + (4842910497479779127/24159502793750000000000000000000 : ℝ)*base71 + (282172946408807/3166850000000000000000000000 : ℝ)*base72 + (7070773371863/529575000000000000000000000 : ℝ)*base75 + (735353071732827/1266740000000000000000000000 : ℝ)*base77 + (4094243611999118873/10062507532500000000000000000000 : ℝ)*base78 + (51091/100000000000000000 : ℝ)*base87 + (51091/100000000000000000 : ℝ)*base89 + (51091/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((63337/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(63337/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(63549/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(63549/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61031/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61031/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((44137/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(44137/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8973/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8973/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10713/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(10713/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c314063_s2 p hpa hpb X hX hprev1

#print axioms solution
