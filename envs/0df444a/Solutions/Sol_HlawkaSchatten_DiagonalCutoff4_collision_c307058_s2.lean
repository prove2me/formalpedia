-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c307058_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:14:17.759972+00:00
-- url     : https://prove2.me/submissions/c1de5473-4ca0-4bdf-a007-b4a859071ece

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
theorem collision_support_c307058_s2_s2_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-3497480133/10000000000 : ℝ)*x 0 + (1698623291/5000000000 : ℝ)*x 1 + (-5914082753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3497480133/10000000000 : ℝ)^17 ≤ (12657334644311/50000000000000 : ℝ)^13 := by
    have hnat : (3497480133 : ℕ)^17*50000000000000^13 ≤ 12657334644311^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3497480133 10000000000 12657334644311 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1698623291/5000000000 : ℝ)^17 ≤ (761567668551/3125000000000 : ℝ)^13 := by
    have hnat : (1698623291 : ℕ)^17*3125000000000^13 ≤ 761567668551^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1698623291 5000000000 761567668551 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5914082753/10000000000 : ℝ)^17 ≤ (2012606612483/4000000000000 : ℝ)^13 := by
    have hnat : (5914082753 : ℕ)^17*4000000000000^13 ≤ 2012606612483^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5914082753 10000000000 2012606612483 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3497480133/10000000000 : ℝ), (1698623291/5000000000 : ℝ), (-5914082753/10000000000 : ℝ)] ![(12657334644311/50000000000000 : ℝ), (761567668551/3125000000000 : ℝ), (2012606612483/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3497480133/10000000000 : ℝ)|^17 ≤ (12657334644311/50000000000000 : ℝ)^13
        have hw : |(-3497480133/10000000000 : ℝ)|=(3497480133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1698623291/5000000000 : ℝ)|^17 ≤ (761567668551/3125000000000 : ℝ)^13
        have hw : |(1698623291/5000000000 : ℝ)|=(1698623291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5914082753/10000000000 : ℝ)|^17 ≤ (2012606612483/4000000000000 : ℝ)^13
        have hw : |(-5914082753/10000000000 : ℝ)|=(5914082753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307058_s2_s2_2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5576934697/10000000000 : ℝ)*x 0 + (667672163/1250000000 : ℝ)*x 1 + (204314519/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5576934697/10000000000 : ℝ)^17 ≤ (931951730689/2000000000000 : ℝ)^13 := by
    have hnat : (5576934697 : ℕ)^17*2000000000000^13 ≤ 931951730689^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5576934697 10000000000 931951730689 2000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (667672163/1250000000 : ℝ)^17 ≤ (22020352312087/50000000000000 : ℝ)^13 := by
    have hnat : (667672163 : ℕ)^17*50000000000000^13 ≤ 22020352312087^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      667672163 1250000000 22020352312087 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (204314519/1250000000 : ℝ)^17 ≤ (1872341765443/20000000000000 : ℝ)^13 := by
    have hnat : (204314519 : ℕ)^17*20000000000000^13 ≤ 1872341765443^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204314519 1250000000 1872341765443 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5576934697/10000000000 : ℝ), (667672163/1250000000 : ℝ), (204314519/1250000000 : ℝ)] ![(931951730689/2000000000000 : ℝ), (22020352312087/50000000000000 : ℝ), (1872341765443/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5576934697/10000000000 : ℝ)|^17 ≤ (931951730689/2000000000000 : ℝ)^13
        have hw : |(5576934697/10000000000 : ℝ)|=(5576934697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(667672163/1250000000 : ℝ)|^17 ≤ (22020352312087/50000000000000 : ℝ)^13
        have hw : |(667672163/1250000000 : ℝ)|=(667672163/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(204314519/1250000000 : ℝ)|^17 ≤ (1872341765443/20000000000000 : ℝ)^13
        have hw : |(204314519/1250000000 : ℝ)|=(204314519/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307058_s2_s2_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1526896707/5000000000 : ℝ)*x 0 + (2765217231/10000000000 : ℝ)*x 1 + (-105967791/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1526896707/5000000000 : ℝ)^17 ≤ (2119965427479/10000000000000 : ℝ)^13 := by
    have hnat : (1526896707 : ℕ)^17*10000000000000^13 ≤ 2119965427479^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1526896707 5000000000 2119965427479 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2765217231/10000000000 : ℝ)^17 ≤ (18618883753689/100000000000000 : ℝ)^13 := by
    have hnat : (2765217231 : ℕ)^17*100000000000000^13 ≤ 18618883753689^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2765217231 10000000000 18618883753689 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105967791/156250000 : ℝ)^17 ≤ (60181461958191/100000000000000 : ℝ)^13 := by
    have hnat : (105967791 : ℕ)^17*100000000000000^13 ≤ 60181461958191^13*156250000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105967791 156250000 60181461958191 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1526896707/5000000000 : ℝ), (2765217231/10000000000 : ℝ), (-105967791/156250000 : ℝ)] ![(2119965427479/10000000000000 : ℝ), (18618883753689/100000000000000 : ℝ), (60181461958191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1526896707/5000000000 : ℝ)|^17 ≤ (2119965427479/10000000000000 : ℝ)^13
        have hw : |(-1526896707/5000000000 : ℝ)|=(1526896707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2765217231/10000000000 : ℝ)|^17 ≤ (18618883753689/100000000000000 : ℝ)^13
        have hw : |(2765217231/10000000000 : ℝ)|=(2765217231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-105967791/156250000 : ℝ)|^17 ≤ (60181461958191/100000000000000 : ℝ)^13
        have hw : |(-105967791/156250000 : ℝ)|=(105967791/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307058_s2_s2_8 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1591037249/5000000000 : ℝ)*x 0 + (-1398737857/5000000000 : ℝ)*x 1 + (-832007307/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1591037249/5000000000 : ℝ)^17 ≤ (11185828210009/50000000000000 : ℝ)^13 := by
    have hnat : (1591037249 : ℕ)^17*50000000000000^13 ≤ 11185828210009^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1591037249 5000000000 11185828210009 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1398737857/5000000000 : ℝ)^17 ≤ (18903428490971/100000000000000 : ℝ)^13 := by
    have hnat : (1398737857 : ℕ)^17*100000000000000^13 ≤ 18903428490971^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1398737857 5000000000 18903428490971 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (832007307/1250000000 : ℝ)^17 ≤ (29362457538943/50000000000000 : ℝ)^13 := by
    have hnat : (832007307 : ℕ)^17*50000000000000^13 ≤ 29362457538943^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832007307 1250000000 29362457538943 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1591037249/5000000000 : ℝ), (-1398737857/5000000000 : ℝ), (-832007307/1250000000 : ℝ)] ![(11185828210009/50000000000000 : ℝ), (18903428490971/100000000000000 : ℝ), (29362457538943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1591037249/5000000000 : ℝ)|^17 ≤ (11185828210009/50000000000000 : ℝ)^13
        have hw : |(1591037249/5000000000 : ℝ)|=(1591037249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1398737857/5000000000 : ℝ)|^17 ≤ (18903428490971/100000000000000 : ℝ)^13
        have hw : |(-1398737857/5000000000 : ℝ)|=(1398737857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-832007307/1250000000 : ℝ)|^17 ≤ (29362457538943/50000000000000 : ℝ)^13
        have hw : |(-832007307/1250000000 : ℝ)|=(832007307/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307058_s2_s2_9 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1391175139/2500000000 : ℝ)*x 0 + (281248501/500000000 : ℝ)*x 1 + (305976599/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1391175139/2500000000 : ℝ)^17 ≤ (46463957680239/100000000000000 : ℝ)^13 := by
    have hnat : (1391175139 : ℕ)^17*100000000000000^13 ≤ 46463957680239^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1391175139 2500000000 46463957680239 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281248501/500000000 : ℝ)^17 ≤ (294519558543/625000000000 : ℝ)^13 := by
    have hnat : (281248501 : ℕ)^17*625000000000^13 ≤ 294519558543^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281248501 500000000 294519558543 625000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (305976599/2500000000 : ℝ)^17 ≤ (3206456470589/50000000000000 : ℝ)^13 := by
    have hnat : (305976599 : ℕ)^17*50000000000000^13 ≤ 3206456470589^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      305976599 2500000000 3206456470589 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1391175139/2500000000 : ℝ), (281248501/500000000 : ℝ), (305976599/2500000000 : ℝ)] ![(46463957680239/100000000000000 : ℝ), (294519558543/625000000000 : ℝ), (3206456470589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1391175139/2500000000 : ℝ)|^17 ≤ (46463957680239/100000000000000 : ℝ)^13
        have hw : |(1391175139/2500000000 : ℝ)|=(1391175139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281248501/500000000 : ℝ)|^17 ≤ (294519558543/625000000000 : ℝ)^13
        have hw : |(281248501/500000000 : ℝ)|=(281248501/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(305976599/2500000000 : ℝ)|^17 ≤ (3206456470589/50000000000000 : ℝ)^13
        have hw : |(305976599/2500000000 : ℝ)|=(305976599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307058_s2_s2_13 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2010514817/5000000000 : ℝ)*x 0 + (7550675749/10000000000 : ℝ)*x 1 + (-136961113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2010514817/5000000000 : ℝ)^17 ≤ (30380498550659/100000000000000 : ℝ)^13 := by
    have hnat : (2010514817 : ℕ)^17*100000000000000^13 ≤ 30380498550659^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010514817 5000000000 30380498550659 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7550675749/10000000000 : ℝ)^17 ≤ (34626851188433/50000000000000 : ℝ)^13 := by
    have hnat : (7550675749 : ℕ)^17*50000000000000^13 ≤ 34626851188433^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7550675749 10000000000 34626851188433 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (136961113/10000000000 : ℝ)^17 ≤ (182899533093/50000000000000 : ℝ)^13 := by
    have hnat : (136961113 : ℕ)^17*50000000000000^13 ≤ 182899533093^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136961113 10000000000 182899533093 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2010514817/5000000000 : ℝ), (7550675749/10000000000 : ℝ), (-136961113/10000000000 : ℝ)] ![(30380498550659/100000000000000 : ℝ), (34626851188433/50000000000000 : ℝ), (182899533093/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2010514817/5000000000 : ℝ)|^17 ≤ (30380498550659/100000000000000 : ℝ)^13
        have hw : |(2010514817/5000000000 : ℝ)|=(2010514817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7550675749/10000000000 : ℝ)|^17 ≤ (34626851188433/50000000000000 : ℝ)^13
        have hw : |(7550675749/10000000000 : ℝ)|=(7550675749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-136961113/10000000000 : ℝ)|^17 ≤ (182899533093/50000000000000 : ℝ)^13
        have hw : |(-136961113/10000000000 : ℝ)|=(136961113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307058_s2_s2_14 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2785373867/10000000000 : ℝ)*x 0 + (1482028551/5000000000 : ℝ)*x 1 + (-1367288417/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2785373867/10000000000 : ℝ)^17 ≤ (3759312375039/20000000000000 : ℝ)^13 := by
    have hnat : (2785373867 : ℕ)^17*20000000000000^13 ≤ 3759312375039^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2785373867 10000000000 3759312375039 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1482028551/5000000000 : ℝ)^17 ≤ (4077745530903/20000000000000 : ℝ)^13 := by
    have hnat : (1482028551 : ℕ)^17*20000000000000^13 ≤ 4077745530903^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1482028551 5000000000 4077745530903 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1367288417/2000000000 : ℝ)^17 ≤ (60814710451021/100000000000000 : ℝ)^13 := by
    have hnat : (1367288417 : ℕ)^17*100000000000000^13 ≤ 60814710451021^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367288417 2000000000 60814710451021 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2785373867/10000000000 : ℝ), (1482028551/5000000000 : ℝ), (-1367288417/2000000000 : ℝ)] ![(3759312375039/20000000000000 : ℝ), (4077745530903/20000000000000 : ℝ), (60814710451021/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2785373867/10000000000 : ℝ)|^17 ≤ (3759312375039/20000000000000 : ℝ)^13
        have hw : |(-2785373867/10000000000 : ℝ)|=(2785373867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1482028551/5000000000 : ℝ)|^17 ≤ (4077745530903/20000000000000 : ℝ)^13
        have hw : |(1482028551/5000000000 : ℝ)|=(1482028551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1367288417/2000000000 : ℝ)|^17 ≤ (60814710451021/100000000000000 : ℝ)^13
        have hw : |(-1367288417/2000000000 : ℝ)|=(1367288417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307058_s2_s2_15 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (708875997/2500000000 : ℝ)*x 0 + (-384552317/1250000000 : ℝ)*x 1 + (-1677640809/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (708875997/2500000000 : ℝ)^17 ≤ (4810041389333/25000000000000 : ℝ)^13 := by
    have hnat : (708875997 : ℕ)^17*25000000000000^13 ≤ 4810041389333^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708875997 2500000000 4810041389333 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (384552317/1250000000 : ℝ)^17 ≤ (21405280980511/100000000000000 : ℝ)^13 := by
    have hnat : (384552317 : ℕ)^17*100000000000000^13 ≤ 21405280980511^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384552317 1250000000 21405280980511 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1677640809/2500000000 : ℝ)^17 ≤ (59354553445079/100000000000000 : ℝ)^13 := by
    have hnat : (1677640809 : ℕ)^17*100000000000000^13 ≤ 59354553445079^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1677640809 2500000000 59354553445079 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(708875997/2500000000 : ℝ), (-384552317/1250000000 : ℝ), (-1677640809/2500000000 : ℝ)] ![(4810041389333/25000000000000 : ℝ), (21405280980511/100000000000000 : ℝ), (59354553445079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(708875997/2500000000 : ℝ)|^17 ≤ (4810041389333/25000000000000 : ℝ)^13
        have hw : |(708875997/2500000000 : ℝ)|=(708875997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-384552317/1250000000 : ℝ)|^17 ≤ (21405280980511/100000000000000 : ℝ)^13
        have hw : |(-384552317/1250000000 : ℝ)|=(384552317/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1677640809/2500000000 : ℝ)|^17 ≤ (59354553445079/100000000000000 : ℝ)^13
        have hw : |(-1677640809/2500000000 : ℝ)|=(1677640809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307058_s2_s2_16 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3110926621/5000000000 : ℝ)*x 0 + (5191280433/10000000000 : ℝ)*x 1 + (820968607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3110926621/5000000000 : ℝ)^17 ≤ (53766338170453/100000000000000 : ℝ)^13 := by
    have hnat : (3110926621 : ℕ)^17*100000000000000^13 ≤ 53766338170453^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3110926621 5000000000 53766338170453 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5191280433/10000000000 : ℝ)^17 ≤ (42429375625717/100000000000000 : ℝ)^13 := by
    have hnat : (5191280433 : ℕ)^17*100000000000000^13 ≤ 42429375625717^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5191280433 10000000000 42429375625717 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (820968607/10000000000 : ℝ)^17 ≤ (1902143097799/50000000000000 : ℝ)^13 := by
    have hnat : (820968607 : ℕ)^17*50000000000000^13 ≤ 1902143097799^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      820968607 10000000000 1902143097799 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3110926621/5000000000 : ℝ), (5191280433/10000000000 : ℝ), (820968607/10000000000 : ℝ)] ![(53766338170453/100000000000000 : ℝ), (42429375625717/100000000000000 : ℝ), (1902143097799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3110926621/5000000000 : ℝ)|^17 ≤ (53766338170453/100000000000000 : ℝ)^13
        have hw : |(3110926621/5000000000 : ℝ)|=(3110926621/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5191280433/10000000000 : ℝ)|^17 ≤ (42429375625717/100000000000000 : ℝ)^13
        have hw : |(5191280433/10000000000 : ℝ)|=(5191280433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(820968607/10000000000 : ℝ)|^17 ≤ (1902143097799/50000000000000 : ℝ)^13
        have hw : |(820968607/10000000000 : ℝ)|=(820968607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307058_s2_s2_20 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1119774847/2500000000 : ℝ)*x 0 + (7111563441/10000000000 : ℝ)*x 1 + (-145677337/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1119774847/2500000000 : ℝ)^17 ≤ (17491810546947/50000000000000 : ℝ)^13 := by
    have hnat : (1119774847 : ℕ)^17*50000000000000^13 ≤ 17491810546947^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119774847 2500000000 17491810546947 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7111563441/10000000000 : ℝ)^17 ≤ (64034774600551/100000000000000 : ℝ)^13 := by
    have hnat : (7111563441 : ℕ)^17*100000000000000^13 ≤ 64034774600551^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7111563441 10000000000 64034774600551 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (145677337/5000000000 : ℝ)^17 ≤ (490802145149/50000000000000 : ℝ)^13 := by
    have hnat : (145677337 : ℕ)^17*50000000000000^13 ≤ 490802145149^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      145677337 5000000000 490802145149 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1119774847/2500000000 : ℝ), (7111563441/10000000000 : ℝ), (-145677337/5000000000 : ℝ)] ![(17491810546947/50000000000000 : ℝ), (64034774600551/100000000000000 : ℝ), (490802145149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1119774847/2500000000 : ℝ)|^17 ≤ (17491810546947/50000000000000 : ℝ)^13
        have hw : |(1119774847/2500000000 : ℝ)|=(1119774847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7111563441/10000000000 : ℝ)|^17 ≤ (64034774600551/100000000000000 : ℝ)^13
        have hw : |(7111563441/10000000000 : ℝ)|=(7111563441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-145677337/5000000000 : ℝ)|^17 ≤ (490802145149/50000000000000 : ℝ)^13
        have hw : |(-145677337/5000000000 : ℝ)|=(145677337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307058_s2_s2_21 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-851062243/2500000000 : ℝ)*x 0 + (41556637/125000000 : ℝ)*x 1 + (-3026838857/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (851062243/2500000000 : ℝ)^17 ≤ (24435873794981/100000000000000 : ℝ)^13 := by
    have hnat : (851062243 : ℕ)^17*100000000000000^13 ≤ 24435873794981^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      851062243 2500000000 24435873794981 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41556637/125000000 : ℝ)^17 ≤ (94761186637/400000000000 : ℝ)^13 := by
    have hnat : (41556637 : ℕ)^17*400000000000^13 ≤ 94761186637^13*125000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41556637 125000000 94761186637 400000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3026838857/5000000000 : ℝ)^17 ≤ (51873829526491/100000000000000 : ℝ)^13 := by
    have hnat : (3026838857 : ℕ)^17*100000000000000^13 ≤ 51873829526491^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3026838857 5000000000 51873829526491 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-851062243/2500000000 : ℝ), (41556637/125000000 : ℝ), (-3026838857/5000000000 : ℝ)] ![(24435873794981/100000000000000 : ℝ), (94761186637/400000000000 : ℝ), (51873829526491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-851062243/2500000000 : ℝ)|^17 ≤ (24435873794981/100000000000000 : ℝ)^13
        have hw : |(-851062243/2500000000 : ℝ)|=(851062243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41556637/125000000 : ℝ)|^17 ≤ (94761186637/400000000000 : ℝ)^13
        have hw : |(41556637/125000000 : ℝ)|=(41556637/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3026838857/5000000000 : ℝ)|^17 ≤ (51873829526491/100000000000000 : ℝ)^13
        have hw : |(-3026838857/5000000000 : ℝ)|=(3026838857/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307058_s2_s2_22 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3338321219/10000000000 : ℝ)*x 0 + (-3211895917/10000000000 : ℝ)*x 1 + (-1240272399/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3338321219/10000000000 : ℝ)^17 ≤ (23818883020019/100000000000000 : ℝ)^13 := by
    have hnat : (3338321219 : ℕ)^17*100000000000000^13 ≤ 23818883020019^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3338321219 10000000000 23818883020019 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3211895917/10000000000 : ℝ)^17 ≤ (22646221966219/100000000000000 : ℝ)^13 := by
    have hnat : (3211895917 : ℕ)^17*100000000000000^13 ≤ 22646221966219^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3211895917 10000000000 22646221966219 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1240272399/2000000000 : ℝ)^17 ≤ (53534894993957/100000000000000 : ℝ)^13 := by
    have hnat : (1240272399 : ℕ)^17*100000000000000^13 ≤ 53534894993957^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1240272399 2000000000 53534894993957 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3338321219/10000000000 : ℝ), (-3211895917/10000000000 : ℝ), (-1240272399/2000000000 : ℝ)] ![(23818883020019/100000000000000 : ℝ), (22646221966219/100000000000000 : ℝ), (53534894993957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3338321219/10000000000 : ℝ)|^17 ≤ (23818883020019/100000000000000 : ℝ)^13
        have hw : |(3338321219/10000000000 : ℝ)|=(3338321219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3211895917/10000000000 : ℝ)|^17 ≤ (22646221966219/100000000000000 : ℝ)^13
        have hw : |(-3211895917/10000000000 : ℝ)|=(3211895917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1240272399/2000000000 : ℝ)|^17 ≤ (53534894993957/100000000000000 : ℝ)^13
        have hw : |(-1240272399/2000000000 : ℝ)|=(1240272399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307058_s2_s2_23 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6587432273/10000000000 : ℝ)*x 0 + (2136053531/5000000000 : ℝ)*x 1 + (805161747/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6587432273/10000000000 : ℝ)^17 ≤ (57934401002449/100000000000000 : ℝ)^13 := by
    have hnat : (6587432273 : ℕ)^17*100000000000000^13 ≤ 57934401002449^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6587432273 10000000000 57934401002449 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2136053531/5000000000 : ℝ)^17 ≤ (4110584353899/12500000000000 : ℝ)^13 := by
    have hnat : (2136053531 : ℕ)^17*12500000000000^13 ≤ 4110584353899^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136053531 5000000000 4110584353899 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (805161747/5000000000 : ℝ)^17 ≤ (2295231038987/25000000000000 : ℝ)^13 := by
    have hnat : (805161747 : ℕ)^17*25000000000000^13 ≤ 2295231038987^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      805161747 5000000000 2295231038987 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6587432273/10000000000 : ℝ), (2136053531/5000000000 : ℝ), (805161747/5000000000 : ℝ)] ![(57934401002449/100000000000000 : ℝ), (4110584353899/12500000000000 : ℝ), (2295231038987/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6587432273/10000000000 : ℝ)|^17 ≤ (57934401002449/100000000000000 : ℝ)^13
        have hw : |(6587432273/10000000000 : ℝ)|=(6587432273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2136053531/5000000000 : ℝ)|^17 ≤ (4110584353899/12500000000000 : ℝ)^13
        have hw : |(2136053531/5000000000 : ℝ)|=(2136053531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(805161747/5000000000 : ℝ)|^17 ≤ (2295231038987/25000000000000 : ℝ)^13
        have hw : |(805161747/5000000000 : ℝ)|=(805161747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307058_s2_s2_27 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1488577207/5000000000 : ℝ)*x 0 + (2073708199/2500000000 : ℝ)*x 1 + (-16790523/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1488577207/5000000000 : ℝ)^17 ≤ (20506620142923/100000000000000 : ℝ)^13 := by
    have hnat : (1488577207 : ℕ)^17*100000000000000^13 ≤ 20506620142923^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1488577207 5000000000 20506620142923 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2073708199/2500000000 : ℝ)^17 ≤ (78311468922899/100000000000000 : ℝ)^13 := by
    have hnat : (2073708199 : ℕ)^17*100000000000000^13 ≤ 78311468922899^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073708199 2500000000 78311468922899 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16790523/500000000 : ℝ)^17 ≤ (590955464807/50000000000000 : ℝ)^13 := by
    have hnat : (16790523 : ℕ)^17*50000000000000^13 ≤ 590955464807^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16790523 500000000 590955464807 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1488577207/5000000000 : ℝ), (2073708199/2500000000 : ℝ), (-16790523/500000000 : ℝ)] ![(20506620142923/100000000000000 : ℝ), (78311468922899/100000000000000 : ℝ), (590955464807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1488577207/5000000000 : ℝ)|^17 ≤ (20506620142923/100000000000000 : ℝ)^13
        have hw : |(1488577207/5000000000 : ℝ)|=(1488577207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2073708199/2500000000 : ℝ)|^17 ≤ (78311468922899/100000000000000 : ℝ)^13
        have hw : |(2073708199/2500000000 : ℝ)|=(2073708199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-16790523/500000000 : ℝ)|^17 ≤ (590955464807/50000000000000 : ℝ)^13
        have hw : |(-16790523/500000000 : ℝ)|=(16790523/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c307058_s2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((16659/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16659/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15027/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15027/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-62563/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-62563/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((52037/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(52037/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8843/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8843/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-1241/6250 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-1241/6250 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4817/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4817/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4817/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4817/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base18 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s2_pow0 : (16659/20000 : ℝ) ^ (135/32 : ℝ) ≤ (23124967227839439849/50000000000000000000 : ℝ) := by
    have hpowers : (16659/20000 : ℝ)^135 ≤ (23124967227839439849/50000000000000000000 : ℝ)^32 := by
      have hnat : (16659 : ℕ)^135*50000000000000000000^32 ≤ 23124967227839439849^32*20000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16659 20000 23124967227839439849 50000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16659/20000 : ℝ)) (X := (23124967227839439849/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner0a : (73124967227839439849/50000000000000000000 : ℝ) ≤ (2735733569092977/2500000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (73124967227839439849/50000000000000000000 : ℝ)^32 ≤ (2735733569092977/2500000000000000 : ℝ)^135 := by
      have hnat : (73124967227839439849 : ℕ)^32*2500000000000000^135 ≤ 2735733569092977^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        73124967227839439849 50000000000000000000 2735733569092977 2500000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2735733569092977/2500000000000000 : ℝ)) (X := (73124967227839439849/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner0b : (48124967227839439849/25000000000000000000 : ℝ) ≤ (233588008463027/200000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (48124967227839439849/25000000000000000000 : ℝ)^32 ≤ (233588008463027/200000000000000 : ℝ)^135 := by
      have hnat : (48124967227839439849 : ℕ)^32*200000000000000^135 ≤ 233588008463027^135*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48124967227839439849 25000000000000000000 233588008463027 200000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (233588008463027/200000000000000 : ℝ)) (X := (48124967227839439849/25000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(235733569092977/2082375000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(368233073389721/4164750000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (16659/20000 : ℝ)) (alpha := (235733569092977/2082375000000000 : ℝ)) (beta := (368233073389721/4164750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (16659/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(235733569092977/2082375000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(368233073389721/4164750000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (15027/20000 : ℝ) ^ (135/32 : ℝ) ≤ (7484273897825062579/25000000000000000000 : ℝ) := by
    have hpowers : (15027/20000 : ℝ)^135 ≤ (7484273897825062579/25000000000000000000 : ℝ)^32 := by
      have hnat : (15027 : ℕ)^135*25000000000000000000^32 ≤ 7484273897825062579^32*20000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15027 20000 7484273897825062579 25000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15027/20000 : ℝ)) (X := (7484273897825062579/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner1a : (32484273897825062579/25000000000000000000 : ℝ) ≤ (2660106220437733/2500000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (32484273897825062579/25000000000000000000 : ℝ)^32 ≤ (2660106220437733/2500000000000000 : ℝ)^135 := by
      have hnat : (32484273897825062579 : ℕ)^32*2500000000000000^135 ≤ 2660106220437733^135*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32484273897825062579 25000000000000000000 2660106220437733 2500000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2660106220437733/2500000000000000 : ℝ)) (X := (32484273897825062579/25000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner1b : (19984273897825062579/12500000000000000000 : ℝ) ≤ (2794106961853937/2500000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (19984273897825062579/12500000000000000000 : ℝ)^32 ≤ (2794106961853937/2500000000000000 : ℝ)^135 := by
      have hnat : (19984273897825062579 : ℕ)^32*2500000000000000^135 ≤ 2794106961853937^135*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19984273897825062579 12500000000000000000 2794106961853937 2500000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2794106961853937/2500000000000000 : ℝ)) (X := (19984273897825062579/12500000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(53368740145911/626125000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(33500185354051/469593750000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (15027/20000 : ℝ)) (alpha := (53368740145911/626125000000000 : ℝ)) (beta := (33500185354051/469593750000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (15027/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(53368740145911/626125000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(33500185354051/469593750000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (62563/100000 : ℝ) ^ (135/32 : ℝ) ≤ (1728322338737593831/12500000000000000000 : ℝ) := by
    have hpowers : (62563/100000 : ℝ)^135 ≤ (1728322338737593831/12500000000000000000 : ℝ)^32 := by
      have hnat : (62563 : ℕ)^135*12500000000000000000^32 ≤ 1728322338737593831^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        62563 100000 1728322338737593831 12500000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (62563/100000 : ℝ)) (X := (1728322338737593831/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner2a : (14228322338737593831/12500000000000000000 : ℝ) ≤ (10311737189848683/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (14228322338737593831/12500000000000000000 : ℝ)^32 ≤ (10311737189848683/10000000000000000 : ℝ)^135 := by
      have hnat : (14228322338737593831 : ℕ)^32*10000000000000000^135 ≤ 10311737189848683^135*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14228322338737593831 12500000000000000000 10311737189848683 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10311737189848683/10000000000000000 : ℝ)) (X := (14228322338737593831/12500000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner2b : (7978322338737593831/6250000000000000000 : ℝ) ≤ (10595791580277819/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (7978322338737593831/6250000000000000000 : ℝ)^32 ≤ (10595791580277819/10000000000000000 : ℝ)^135 := by
      have hnat : (7978322338737593831 : ℕ)^32*10000000000000000^135 ≤ 10595791580277819^135*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7978322338737593831 6250000000000000000 10595791580277819 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10595791580277819/10000000000000000 : ℝ)) (X := (7978322338737593831/6250000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(311737189848683/6256300000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(17753399401821/391018750000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (62563/100000 : ℝ)) (alpha := (311737189848683/6256300000000000 : ℝ)) (beta := (17753399401821/391018750000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (62563/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(311737189848683/6256300000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(17753399401821/391018750000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-3497480133/10000000000 : ℝ)*X 0 0+(1698623291/5000000000 : ℝ)*X 0 1+(-5914082753/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307058_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((5576934697/10000000000 : ℝ)*X 2 0+(667672163/1250000000 : ℝ)*X 2 1+(204314519/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307058_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-1526896707/5000000000 : ℝ)*X 0 0+(2765217231/10000000000 : ℝ)*X 0 1+(-105967791/156250000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307058_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((1591037249/5000000000 : ℝ)*X 1 0+(-1398737857/5000000000 : ℝ)*X 1 1+(-832007307/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307058_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((1391175139/2500000000 : ℝ)*X 2 0+(281248501/500000000 : ℝ)*X 2 1+(305976599/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307058_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((2010514817/5000000000 : ℝ)*X 0 0+(7550675749/10000000000 : ℝ)*X 0 1+(-136961113/10000000000 : ℝ)*X 0 2+(2010514817/5000000000 : ℝ)*X 1 0+(7550675749/10000000000 : ℝ)*X 1 1+(-136961113/10000000000 : ℝ)*X 1 2+(2010514817/5000000000 : ℝ)*X 2 0+(7550675749/10000000000 : ℝ)*X 2 1+(-136961113/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307058_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-2785373867/10000000000 : ℝ)*X 0 0+(1482028551/5000000000 : ℝ)*X 0 1+(-1367288417/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307058_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((708875997/2500000000 : ℝ)*X 1 0+(-384552317/1250000000 : ℝ)*X 1 1+(-1677640809/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307058_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((3110926621/5000000000 : ℝ)*X 2 0+(5191280433/10000000000 : ℝ)*X 2 1+(820968607/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307058_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((1119774847/2500000000 : ℝ)*X 0 0+(7111563441/10000000000 : ℝ)*X 0 1+(-145677337/5000000000 : ℝ)*X 0 2+(1119774847/2500000000 : ℝ)*X 1 0+(7111563441/10000000000 : ℝ)*X 1 1+(-145677337/5000000000 : ℝ)*X 1 2+(1119774847/2500000000 : ℝ)*X 2 0+(7111563441/10000000000 : ℝ)*X 2 1+(-145677337/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307058_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-851062243/2500000000 : ℝ)*X 0 0+(41556637/125000000 : ℝ)*X 0 1+(-3026838857/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307058_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((3338321219/10000000000 : ℝ)*X 1 0+(-3211895917/10000000000 : ℝ)*X 1 1+(-1240272399/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307058_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((6587432273/10000000000 : ℝ)*X 2 0+(2136053531/5000000000 : ℝ)*X 2 1+(805161747/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307058_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((1488577207/5000000000 : ℝ)*X 0 0+(2073708199/2500000000 : ℝ)*X 0 1+(-16790523/500000000 : ℝ)*X 0 2+(1488577207/5000000000 : ℝ)*X 1 0+(2073708199/2500000000 : ℝ)*X 1 1+(-16790523/500000000 : ℝ)*X 1 2+(1488577207/5000000000 : ℝ)*X 2 0+(2073708199/2500000000 : ℝ)*X 2 1+(-16790523/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307058_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((52037/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(52037/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (251532336295016369681656191/78344516750000000000000000000000 : ℝ) := by norm_num
    linear_combination (140117369501/1000000000000 : ℝ)*(base5) + (1228529/500000000000 : ℝ)*(base8) + (462719/1000000000000 : ℝ)*(base15) + (177353/200000000000 : ℝ)*(base59) + (1502473475587/1000000000000 : ℝ)*(base60) + (7569648763839/1000000000000 : ℝ)*(major_s2_0) + (7569648763839/1000000000000 : ℝ)*(major_s2_1) + (7569648763839/1000000000000 : ℝ)*(major_s2_2) + (10269724264019/1000000000000 : ℝ)*(sp_s2_7) + (5134863129179/500000000000 : ℝ)*(sp_s2_8) + (10409844090577/1000000000000 : ℝ)*(sp_s2_9) + (4729390482491/1000000000000 : ℝ)*(sp_s2_13) + (8991939/500000000000 : ℝ)*(sp_s2_20) + (4390053/100000000000 : ℝ)*(sp_s2_27) + (12173924341/2500000000 : ℝ)*(f.failure) + (10269726721077/1000000000000 : ℝ)*(f.sum) + (30384466449839535043/156689033500000000000000000000000 : ℝ)*base63 + (819533461154819/1564075000000000000000000000 : ℝ)*base64 + (291231646953079/1252250000000000000000000000 : ℝ)*base67 + (1840170727081097/6256300000000000000000000000 : ℝ)*base68 + (5956385262992375023/28951028250000000000000000000000 : ℝ)*base70 + (52332989301829/115687500000000000000000000 : ℝ)*base73 + (33949598401727/313062500000000000000000000 : ℝ)*base75 + (145553610706259/462750000000000000000000000 : ℝ)*base77 + (6963002022403769/289739343750000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (9/125000000000000 : ℝ)*base87 + (9/125000000000000 : ℝ)*base89 + (9/125000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8843/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8843/20000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (609479315760872556374870115779/72507850252125000000000000000000000 : ℝ) := by norm_num
    linear_combination (3965052964363/1000000000000 : ℝ)*(base5) + (7734677/1000000000000 : ℝ)*(base18) + (2993879/1000000000000 : ℝ)*(base49) + (1799212274031/500000000000 : ℝ)*(base60) + (3285576704651/500000000000 : ℝ)*(major_s2_0) + (3285576704651/500000000000 : ℝ)*(major_s2_1) + (3285576704651/500000000000 : ℝ)*(major_s2_2) + (3646091/1000000000000 : ℝ)*(sp_s2_2) + (78770333/1000000000000 : ℝ)*(sp_s2_7) + (509361/62500000000 : ℝ)*(sp_s2_9) + (8914989508819/1000000000000 : ℝ)*(sp_s2_14) + (356602421779/40000000000 : ℝ)*(sp_s2_15) + (12880109447649/1000000000000 : ℝ)*(sp_s2_16) + (4096605831/15625000000 : ℝ)*(sp_s2_20) + (4227235737547/1000000000000 : ℝ)*(f.failure) + (557191767447/62500000000 : ℝ)*(f.sum) + (10921556990105461147/19586129187500000000000000000000 : ℝ)*base62 + (1517893949281539/3128150000000000000000000000 : ℝ)*base64 + (594863749905259/3756750000000000000000000000 : ℝ)*base66 + (1778139240547613/3128150000000000000000000000 : ℝ)*base68 + (30115147260044459069/65139813562500000000000000000000 : ℝ)*base70 + (592820907089579/2082375000000000000000000000 : ℝ)*base72 + (594853057521681/1252250000000000000000000000 : ℝ)*base74 + (2028865138539767/4164750000000000000000000000 : ℝ)*base76 + (2042856278155430999/20861232750000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base85 + (757/12500000000000000 : ℝ)*base87 + (757/12500000000000000 : ℝ)*base89 + (757/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-1241/6250 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-1241/6250 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2203048444401293550862794405037/435047101512750000000000000000000000 : ℝ) := by norm_num
    linear_combination (664133/500000000000 : ℝ)*(base15) + (383801/500000000000 : ℝ)*(base16) + (151497991131/1000000000000 : ℝ)*(base49) + (12400251821/50000000000 : ℝ)*(base60) + (2040954547741/500000000000 : ℝ)*(major_s2_0) + (2040954547741/500000000000 : ℝ)*(major_s2_1) + (2040954547741/500000000000 : ℝ)*(major_s2_2) + (82481917/500000000000 : ℝ)*(sp_s2_0) + (23608513/500000000000 : ℝ)*(sp_s2_2) + (55536767/1000000000000 : ℝ)*(sp_s2_13) + (5537751498311/1000000000000 : ℝ)*(sp_s2_21) + (2768957183139/500000000000 : ℝ)*(sp_s2_22) + (5537869245119/1000000000000 : ℝ)*(sp_s2_23) + (2625844504071/1000000000000 : ℝ)*(sp_s2_27) + (1312950020419/500000000000 : ℝ)*(f.failure) + (1107583292429/200000000000 : ℝ)*(f.sum) + (4503831319594734933/78344516750000000000000000000000 : ℝ)*base62 + (183446759960971/3128150000000000000000000000 : ℝ)*base65 + (1148960660133119/3756750000000000000000000000 : ℝ)*base66 + (57477077149613/3128150000000000000000000000 : ℝ)*base68 + (219320618881528770059/260559254250000000000000000000000 : ℝ)*base71 + (2539990342043497/4164750000000000000000000000 : ℝ)*base73 + (9471024465021/1252250000000000000000000000 : ℝ)*base74 + (243250273830353/4164750000000000000000000000 : ℝ)*base77 + (7484932010063290459/20861232750000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (911/6250000000000000 : ℝ)*base86 + (911/6250000000000000 : ℝ)*base88 + (911/6250000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]])
    (hprev1 : (0 : ℝ) ≤ ((16659/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16659/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15027/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(15027/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-62563/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-62563/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((52037/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(52037/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(8843/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(8843/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-1241/6250 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-1241/6250 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c307058_s2 p hpa hpb X hX hprev1

#print axioms solution
