-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c326063_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:11:59.615707+00:00
-- url     : https://prove2.me/submissions/a9abdafd-fcdf-4023-9ede-70bab79c612a

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
theorem collision_support_c326063_s2_s2_0 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-50122571/400000000 : ℝ)*x 0 + (5289294941/10000000000 : ℝ)*x 1 + (5293883723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (50122571/400000000 : ℝ)^89 ≤ (7948201648823/100000000000000 : ℝ)^73 := by
    have hnat : (50122571 : ℕ)^89*100000000000000^73 ≤ 7948201648823^73*400000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50122571 400000000 7948201648823 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5289294941/10000000000 : ℝ)^89 ≤ (9200313737651/20000000000000 : ℝ)^73 := by
    have hnat : (5289294941 : ℕ)^89*20000000000000^73 ≤ 9200313737651^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289294941 10000000000 9200313737651 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5293883723/10000000000 : ℝ)^89 ≤ (46050229652319/100000000000000 : ℝ)^73 := by
    have hnat : (5293883723 : ℕ)^89*100000000000000^73 ≤ 46050229652319^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293883723 10000000000 46050229652319 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-50122571/400000000 : ℝ), (5289294941/10000000000 : ℝ), (5293883723/10000000000 : ℝ)] ![(7948201648823/100000000000000 : ℝ), (9200313737651/20000000000000 : ℝ), (46050229652319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-50122571/400000000 : ℝ)|^89 ≤ (7948201648823/100000000000000 : ℝ)^73
        have hw : |(-50122571/400000000 : ℝ)|=(50122571/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5289294941/10000000000 : ℝ)|^89 ≤ (9200313737651/20000000000000 : ℝ)^73
        have hw : |(5289294941/10000000000 : ℝ)|=(5289294941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5293883723/10000000000 : ℝ)|^89 ≤ (46050229652319/100000000000000 : ℝ)^73
        have hw : |(5293883723/10000000000 : ℝ)|=(5293883723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326063_s2_s2_1 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (661192263/1250000000 : ℝ)*x 0 + (-125493173/1000000000 : ℝ)*x 1 + (5292278607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661192263/1250000000 : ℝ)^89 ≤ (46004147037149/100000000000000 : ℝ)^73 := by
    have hnat : (661192263 : ℕ)^89*100000000000000^73 ≤ 46004147037149^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661192263 1250000000 46004147037149 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (125493173/1000000000 : ℝ)^89 ≤ (7962645523673/100000000000000 : ℝ)^73 := by
    have hnat : (125493173 : ℕ)^89*100000000000000^73 ≤ 7962645523673^73*1000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125493173 1000000000 7962645523673 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5292278607/10000000000 : ℝ)^89 ≤ (4603320741893/10000000000000 : ℝ)^73 := by
    have hnat : (5292278607 : ℕ)^89*10000000000000^73 ≤ 4603320741893^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5292278607 10000000000 4603320741893 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661192263/1250000000 : ℝ), (-125493173/1000000000 : ℝ), (5292278607/10000000000 : ℝ)] ![(46004147037149/100000000000000 : ℝ), (7962645523673/100000000000000 : ℝ), (4603320741893/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661192263/1250000000 : ℝ)|^89 ≤ (46004147037149/100000000000000 : ℝ)^73
        have hw : |(661192263/1250000000 : ℝ)|=(661192263/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-125493173/1000000000 : ℝ)|^89 ≤ (7962645523673/100000000000000 : ℝ)^73
        have hw : |(-125493173/1000000000 : ℝ)|=(125493173/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5292278607/10000000000 : ℝ)|^89 ≤ (4603320741893/10000000000000 : ℝ)^73
        have hw : |(5292278607/10000000000 : ℝ)|=(5292278607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326063_s2_s2_2 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5293223137/10000000000 : ℝ)*x 0 + (2645930289/5000000000 : ℝ)*x 1 + (-625225787/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293223137/10000000000 : ℝ)^89 ≤ (287770150061/625000000000 : ℝ)^73 := by
    have hnat : (5293223137 : ℕ)^89*625000000000^73 ≤ 287770150061^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293223137 10000000000 287770150061 625000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2645930289/5000000000 : ℝ)^89 ≤ (46028774412767/100000000000000 : ℝ)^73 := by
    have hnat : (2645930289 : ℕ)^89*100000000000000^73 ≤ 46028774412767^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645930289 5000000000 46028774412767 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (625225787/5000000000 : ℝ)^89 ≤ (1585600313801/20000000000000 : ℝ)^73 := by
    have hnat : (625225787 : ℕ)^89*20000000000000^73 ≤ 1585600313801^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625225787 5000000000 1585600313801 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293223137/10000000000 : ℝ), (2645930289/5000000000 : ℝ), (-625225787/5000000000 : ℝ)] ![(287770150061/625000000000 : ℝ), (46028774412767/100000000000000 : ℝ), (1585600313801/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293223137/10000000000 : ℝ)|^89 ≤ (287770150061/625000000000 : ℝ)^73
        have hw : |(5293223137/10000000000 : ℝ)|=(5293223137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2645930289/5000000000 : ℝ)|^89 ≤ (46028774412767/100000000000000 : ℝ)^73
        have hw : |(2645930289/5000000000 : ℝ)|=(2645930289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-625225787/5000000000 : ℝ)|^89 ≤ (1585600313801/20000000000000 : ℝ)^73
        have hw : |(-625225787/5000000000 : ℝ)|=(625225787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326063_s2_s2_6 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2031145361/5000000000 : ℝ)*x 0 + (2030733789/5000000000 : ℝ)*x 1 + (1014953217/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2031145361/5000000000 : ℝ)^89 ≤ (16672172055551/50000000000000 : ℝ)^73 := by
    have hnat : (2031145361 : ℕ)^89*50000000000000^73 ≤ 16672172055551^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2031145361 5000000000 16672172055551 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2030733789/5000000000 : ℝ)^89 ≤ (4167013352303/12500000000000 : ℝ)^73 := by
    have hnat : (2030733789 : ℕ)^89*12500000000000^73 ≤ 4167013352303^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2030733789 5000000000 4167013352303 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1014953217/2500000000 : ℝ)^89 ≤ (33319549060329/100000000000000 : ℝ)^73 := by
    have hnat : (1014953217 : ℕ)^89*100000000000000^73 ≤ 33319549060329^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1014953217 2500000000 33319549060329 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2031145361/5000000000 : ℝ), (2030733789/5000000000 : ℝ), (1014953217/2500000000 : ℝ)] ![(16672172055551/50000000000000 : ℝ), (4167013352303/12500000000000 : ℝ), (33319549060329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2031145361/5000000000 : ℝ)|^89 ≤ (16672172055551/50000000000000 : ℝ)^73
        have hw : |(2031145361/5000000000 : ℝ)|=(2031145361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2030733789/5000000000 : ℝ)|^89 ≤ (4167013352303/12500000000000 : ℝ)^73
        have hw : |(2030733789/5000000000 : ℝ)|=(2030733789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1014953217/2500000000 : ℝ)|^89 ≤ (33319549060329/100000000000000 : ℝ)^73
        have hw : |(1014953217/2500000000 : ℝ)|=(1014953217/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326063_s2_s2_7 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-592378949/5000000000 : ℝ)*x 0 + (937579993/2000000000 : ℝ)*x 1 + (1482211503/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (592378949/5000000000 : ℝ)^89 ≤ (185579301727/2500000000000 : ℝ)^73 := by
    have hnat : (592378949 : ℕ)^89*2500000000000^73 ≤ 185579301727^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      592378949 5000000000 185579301727 2500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (937579993/2000000000 : ℝ)^89 ≤ (9926679656407/25000000000000 : ℝ)^73 := by
    have hnat : (937579993 : ℕ)^89*25000000000000^73 ≤ 9926679656407^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937579993 2000000000 9926679656407 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1482211503/2500000000 : ℝ)^89 ≤ (10574021857053/20000000000000 : ℝ)^73 := by
    have hnat : (1482211503 : ℕ)^89*20000000000000^73 ≤ 10574021857053^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1482211503 2500000000 10574021857053 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-592378949/5000000000 : ℝ), (937579993/2000000000 : ℝ), (1482211503/2500000000 : ℝ)] ![(185579301727/2500000000000 : ℝ), (9926679656407/25000000000000 : ℝ), (10574021857053/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-592378949/5000000000 : ℝ)|^89 ≤ (185579301727/2500000000000 : ℝ)^73
        have hw : |(-592378949/5000000000 : ℝ)|=(592378949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(937579993/2000000000 : ℝ)|^89 ≤ (9926679656407/25000000000000 : ℝ)^73
        have hw : |(937579993/2000000000 : ℝ)|=(937579993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1482211503/2500000000 : ℝ)|^89 ≤ (10574021857053/20000000000000 : ℝ)^73
        have hw : |(1482211503/2500000000 : ℝ)|=(1482211503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326063_s2_s2_8 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (157890319/312500000 : ℝ)*x 0 + (-10328097/156250000 : ℝ)*x 1 + (5927233911/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (157890319/312500000 : ℝ)^89 ≤ (43503117506077/100000000000000 : ℝ)^73 := by
    have hnat : (157890319 : ℕ)^89*100000000000000^73 ≤ 43503117506077^73*312500000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157890319 312500000 43503117506077 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (10328097/156250000 : ℝ)^89 ≤ (56942177209/1562500000000 : ℝ)^73 := by
    have hnat : (10328097 : ℕ)^89*1562500000000^73 ≤ 56942177209^73*156250000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10328097 156250000 56942177209 1562500000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5927233911/10000000000 : ℝ)^89 ≤ (5285258313669/10000000000000 : ℝ)^73 := by
    have hnat : (5927233911 : ℕ)^89*10000000000000^73 ≤ 5285258313669^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5927233911 10000000000 5285258313669 10000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(157890319/312500000 : ℝ), (-10328097/156250000 : ℝ), (5927233911/10000000000 : ℝ)] ![(43503117506077/100000000000000 : ℝ), (56942177209/1562500000000 : ℝ), (5285258313669/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(157890319/312500000 : ℝ)|^89 ≤ (43503117506077/100000000000000 : ℝ)^73
        have hw : |(157890319/312500000 : ℝ)|=(157890319/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-10328097/156250000 : ℝ)|^89 ≤ (56942177209/1562500000000 : ℝ)^73
        have hw : |(-10328097/156250000 : ℝ)|=(10328097/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5927233911/10000000000 : ℝ)|^89 ≤ (5285258313669/10000000000000 : ℝ)^73
        have hw : |(5927233911/10000000000 : ℝ)|=(5927233911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326063_s2_s2_9 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4850735679/10000000000 : ℝ)*x 0 + (6126687123/10000000000 : ℝ)*x 1 + (-325454083/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4850735679/10000000000 : ℝ)^89 ≤ (8278916843319/20000000000000 : ℝ)^73 := by
    have hnat : (4850735679 : ℕ)^89*20000000000000^73 ≤ 8278916843319^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4850735679 10000000000 8278916843319 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6126687123/10000000000 : ℝ)^89 ≤ (13757206257747/25000000000000 : ℝ)^73 := by
    have hnat : (6126687123 : ℕ)^89*25000000000000^73 ≤ 13757206257747^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6126687123 10000000000 13757206257747 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (325454083/5000000000 : ℝ)^89 ≤ (1788295369659/50000000000000 : ℝ)^73 := by
    have hnat : (325454083 : ℕ)^89*50000000000000^73 ≤ 1788295369659^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325454083 5000000000 1788295369659 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4850735679/10000000000 : ℝ), (6126687123/10000000000 : ℝ), (-325454083/5000000000 : ℝ)] ![(8278916843319/20000000000000 : ℝ), (13757206257747/25000000000000 : ℝ), (1788295369659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4850735679/10000000000 : ℝ)|^89 ≤ (8278916843319/20000000000000 : ℝ)^73
        have hw : |(4850735679/10000000000 : ℝ)|=(4850735679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6126687123/10000000000 : ℝ)|^89 ≤ (13757206257747/25000000000000 : ℝ)^73
        have hw : |(6126687123/10000000000 : ℝ)|=(6126687123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-325454083/5000000000 : ℝ)|^89 ≤ (1788295369659/50000000000000 : ℝ)^73
        have hw : |(-325454083/5000000000 : ℝ)|=(325454083/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326063_s2_s2_13 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4469740269/10000000000 : ℝ)*x 0 + (5388352577/10000000000 : ℝ)*x 1 + (270613709/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4469740269/10000000000 : ℝ)^89 ≤ (37465525633347/100000000000000 : ℝ)^73 := by
    have hnat : (4469740269 : ℕ)^89*100000000000000^73 ≤ 37465525633347^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4469740269 10000000000 37465525633347 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5388352577/10000000000 : ℝ)^89 ≤ (9410810820379/20000000000000 : ℝ)^73 := by
    have hnat : (5388352577 : ℕ)^89*20000000000000^73 ≤ 9410810820379^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5388352577 10000000000 9410810820379 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (270613709/1250000000 : ℝ)^89 ≤ (15480420248303/100000000000000 : ℝ)^73 := by
    have hnat : (270613709 : ℕ)^89*100000000000000^73 ≤ 15480420248303^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270613709 1250000000 15480420248303 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4469740269/10000000000 : ℝ), (5388352577/10000000000 : ℝ), (270613709/1250000000 : ℝ)] ![(37465525633347/100000000000000 : ℝ), (9410810820379/20000000000000 : ℝ), (15480420248303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4469740269/10000000000 : ℝ)|^89 ≤ (37465525633347/100000000000000 : ℝ)^73
        have hw : |(4469740269/10000000000 : ℝ)|=(4469740269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5388352577/10000000000 : ℝ)|^89 ≤ (9410810820379/20000000000000 : ℝ)^73
        have hw : |(5388352577/10000000000 : ℝ)|=(5388352577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(270613709/1250000000 : ℝ)|^89 ≤ (15480420248303/100000000000000 : ℝ)^73
        have hw : |(270613709/1250000000 : ℝ)|=(270613709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326063_s2_s2_14 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-332297471/5000000000 : ℝ)*x 0 + (252991621/500000000 : ℝ)*x 1 + (2958958147/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332297471/5000000000 : ℝ)^89 ≤ (458561250471/12500000000000 : ℝ)^73 := by
    have hnat : (332297471 : ℕ)^89*12500000000000^73 ≤ 458561250471^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332297471 5000000000 458561250471 12500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (252991621/500000000 : ℝ)^89 ≤ (8716040793057/20000000000000 : ℝ)^73 := by
    have hnat : (252991621 : ℕ)^89*20000000000000^73 ≤ 8716040793057^73*500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252991621 500000000 8716040793057 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2958958147/5000000000 : ℝ)^89 ≤ (52751306027123/100000000000000 : ℝ)^73 := by
    have hnat : (2958958147 : ℕ)^89*100000000000000^73 ≤ 52751306027123^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2958958147 5000000000 52751306027123 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-332297471/5000000000 : ℝ), (252991621/500000000 : ℝ), (2958958147/5000000000 : ℝ)] ![(458561250471/12500000000000 : ℝ), (8716040793057/20000000000000 : ℝ), (52751306027123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-332297471/5000000000 : ℝ)|^89 ≤ (458561250471/12500000000000 : ℝ)^73
        have hw : |(-332297471/5000000000 : ℝ)|=(332297471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(252991621/500000000 : ℝ)|^89 ≤ (8716040793057/20000000000000 : ℝ)^73
        have hw : |(252991621/500000000 : ℝ)|=(252991621/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2958958147/5000000000 : ℝ)|^89 ≤ (52751306027123/100000000000000 : ℝ)^73
        have hw : |(2958958147/5000000000 : ℝ)|=(2958958147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326063_s2_s2_15 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1176157001/2500000000 : ℝ)*x 0 + (-294995031/2500000000 : ℝ)*x 1 + (2958151791/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1176157001/2500000000 : ℝ)^89 ≤ (19939764036689/50000000000000 : ℝ)^73 := by
    have hnat : (1176157001 : ℕ)^89*50000000000000^73 ≤ 19939764036689^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1176157001 2500000000 19939764036689 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (294995031/2500000000 : ℝ)^89 ≤ (1477338318757/20000000000000 : ℝ)^73 := by
    have hnat : (294995031 : ℕ)^89*20000000000000^73 ≤ 1477338318757^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      294995031 2500000000 1477338318757 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2958151791/5000000000 : ℝ)^89 ≤ (52733780326393/100000000000000 : ℝ)^73 := by
    have hnat : (2958151791 : ℕ)^89*100000000000000^73 ≤ 52733780326393^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2958151791 5000000000 52733780326393 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1176157001/2500000000 : ℝ), (-294995031/2500000000 : ℝ), (2958151791/5000000000 : ℝ)] ![(19939764036689/50000000000000 : ℝ), (1477338318757/20000000000000 : ℝ), (52733780326393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1176157001/2500000000 : ℝ)|^89 ≤ (19939764036689/50000000000000 : ℝ)^73
        have hw : |(1176157001/2500000000 : ℝ)|=(1176157001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-294995031/2500000000 : ℝ)|^89 ≤ (1477338318757/20000000000000 : ℝ)^73
        have hw : |(-294995031/2500000000 : ℝ)|=(294995031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2958151791/5000000000 : ℝ)|^89 ≤ (52733780326393/100000000000000 : ℝ)^73
        have hw : |(2958151791/5000000000 : ℝ)|=(2958151791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326063_s2_s2_16 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5917335273/10000000000 : ℝ)*x 0 + (5062199589/10000000000 : ℝ)*x 1 + (-661838133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5917335273/10000000000 : ℝ)^89 ≤ (52744991821777/100000000000000 : ℝ)^73 := by
    have hnat : (5917335273 : ℕ)^89*100000000000000^73 ≤ 52744991821777^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5917335273 10000000000 52744991821777 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5062199589/10000000000 : ℝ)^89 ≤ (10901265571677/25000000000000 : ℝ)^73 := by
    have hnat : (5062199589 : ℕ)^89*25000000000000^73 ≤ 10901265571677^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5062199589 10000000000 10901265571677 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (661838133/10000000000 : ℝ)^89 ≤ (1824972937171/50000000000000 : ℝ)^73 := by
    have hnat : (661838133 : ℕ)^89*50000000000000^73 ≤ 1824972937171^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661838133 10000000000 1824972937171 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5917335273/10000000000 : ℝ), (5062199589/10000000000 : ℝ), (-661838133/10000000000 : ℝ)] ![(52744991821777/100000000000000 : ℝ), (10901265571677/25000000000000 : ℝ), (1824972937171/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5917335273/10000000000 : ℝ)|^89 ≤ (52744991821777/100000000000000 : ℝ)^73
        have hw : |(5917335273/10000000000 : ℝ)|=(5917335273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5062199589/10000000000 : ℝ)|^89 ≤ (10901265571677/25000000000000 : ℝ)^73
        have hw : |(5062199589/10000000000 : ℝ)|=(5062199589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-661838133/10000000000 : ℝ)|^89 ≤ (1824972937171/50000000000000 : ℝ)^73
        have hw : |(-661838133/10000000000 : ℝ)|=(661838133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326063_s2_s2_20 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (59791201/100000000 : ℝ)*x 0 + (3806657417/10000000000 : ℝ)*x 1 + (43981383/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (59791201/100000000 : ℝ)^89 ≤ (26708596562977/50000000000000 : ℝ)^73 := by
    have hnat : (59791201 : ℕ)^89*50000000000000^73 ≤ 26708596562977^73*100000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59791201 100000000 26708596562977 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3806657417/10000000000 : ℝ)^89 ≤ (30804076062877/100000000000000 : ℝ)^73 := by
    have hnat : (3806657417 : ℕ)^89*100000000000000^73 ≤ 30804076062877^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3806657417 10000000000 30804076062877 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43981383/200000000 : ℝ)^89 ≤ (15778730791087/100000000000000 : ℝ)^73 := by
    have hnat : (43981383 : ℕ)^89*100000000000000^73 ≤ 15778730791087^73*200000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43981383 200000000 15778730791087 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(59791201/100000000 : ℝ), (3806657417/10000000000 : ℝ), (43981383/200000000 : ℝ)] ![(26708596562977/50000000000000 : ℝ), (30804076062877/100000000000000 : ℝ), (15778730791087/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(59791201/100000000 : ℝ)|^89 ≤ (26708596562977/50000000000000 : ℝ)^73
        have hw : |(59791201/100000000 : ℝ)|=(59791201/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3806657417/10000000000 : ℝ)|^89 ≤ (30804076062877/100000000000000 : ℝ)^73
        have hw : |(3806657417/10000000000 : ℝ)|=(3806657417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43981383/200000000 : ℝ)|^89 ≤ (15778730791087/100000000000000 : ℝ)^73
        have hw : |(43981383/200000000 : ℝ)|=(43981383/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326063_s2_s2_21 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-612253463/10000000000 : ℝ)*x 0 + (2832692559/5000000000 : ℝ)*x 1 + (5351383523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (612253463/10000000000 : ℝ)^89 ≤ (1659675459563/50000000000000 : ℝ)^73 := by
    have hnat : (612253463 : ℕ)^89*50000000000000^73 ≤ 1659675459563^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      612253463 10000000000 1659675459563 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2832692559/5000000000 : ℝ)^89 ≤ (10003978147923/20000000000000 : ℝ)^73 := by
    have hnat : (2832692559 : ℕ)^89*20000000000000^73 ≤ 10003978147923^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2832692559 5000000000 10003978147923 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5351383523/10000000000 : ℝ)^89 ≤ (11665189581917/25000000000000 : ℝ)^73 := by
    have hnat : (5351383523 : ℕ)^89*25000000000000^73 ≤ 11665189581917^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351383523 10000000000 11665189581917 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-612253463/10000000000 : ℝ), (2832692559/5000000000 : ℝ), (5351383523/10000000000 : ℝ)] ![(1659675459563/50000000000000 : ℝ), (10003978147923/20000000000000 : ℝ), (11665189581917/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-612253463/10000000000 : ℝ)|^89 ≤ (1659675459563/50000000000000 : ℝ)^73
        have hw : |(-612253463/10000000000 : ℝ)|=(612253463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2832692559/5000000000 : ℝ)|^89 ≤ (10003978147923/20000000000000 : ℝ)^73
        have hw : |(2832692559/5000000000 : ℝ)|=(2832692559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5351383523/10000000000 : ℝ)|^89 ≤ (11665189581917/25000000000000 : ℝ)^73
        have hw : |(5351383523/10000000000 : ℝ)|=(5351383523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326063_s2_s2_22 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5965760123/10000000000 : ℝ)*x 0 + (-30482343/500000000 : ℝ)*x 1 + (1009031577/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5965760123/10000000000 : ℝ)^89 ≤ (1331792770107/2500000000000 : ℝ)^73 := by
    have hnat : (5965760123 : ℕ)^89*2500000000000^73 ≤ 1331792770107^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5965760123 10000000000 1331792770107 2500000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30482343/500000000 : ℝ)^89 ≤ (660425962491/20000000000000 : ℝ)^73 := by
    have hnat : (30482343 : ℕ)^89*20000000000000^73 ≤ 660425962491^73*500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30482343 500000000 660425962491 20000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1009031577/2000000000 : ℝ)^89 ≤ (21713079685661/50000000000000 : ℝ)^73 := by
    have hnat : (1009031577 : ℕ)^89*50000000000000^73 ≤ 21713079685661^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009031577 2000000000 21713079685661 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5965760123/10000000000 : ℝ), (-30482343/500000000 : ℝ), (1009031577/2000000000 : ℝ)] ![(1331792770107/2500000000000 : ℝ), (660425962491/20000000000000 : ℝ), (21713079685661/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5965760123/10000000000 : ℝ)|^89 ≤ (1331792770107/2500000000000 : ℝ)^73
        have hw : |(5965760123/10000000000 : ℝ)|=(5965760123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-30482343/500000000 : ℝ)|^89 ≤ (660425962491/20000000000000 : ℝ)^73
        have hw : |(-30482343/500000000 : ℝ)|=(30482343/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1009031577/2000000000 : ℝ)|^89 ≤ (21713079685661/50000000000000 : ℝ)^73
        have hw : |(1009031577/2000000000 : ℝ)|=(1009031577/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326063_s2_s2_23 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (929613613/2000000000 : ℝ)*x 0 + (5972368967/10000000000 : ℝ)*x 1 + (-1176554193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (929613613/2000000000 : ℝ)^89 ≤ (9823944671759/25000000000000 : ℝ)^73 := by
    have hnat : (929613613 : ℕ)^89*25000000000000^73 ≤ 9823944671759^73*2000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929613613 2000000000 9823944671759 25000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5972368967/10000000000 : ℝ)^89 ≤ (26671834164077/50000000000000 : ℝ)^73 := by
    have hnat : (5972368967 : ℕ)^89*50000000000000^73 ≤ 26671834164077^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5972368967 10000000000 26671834164077 50000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1176554193/10000000000 : ℝ)^89 ≤ (7360552969669/100000000000000 : ℝ)^73 := by
    have hnat : (1176554193 : ℕ)^89*100000000000000^73 ≤ 7360552969669^73*10000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1176554193 10000000000 7360552969669 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(929613613/2000000000 : ℝ), (5972368967/10000000000 : ℝ), (-1176554193/10000000000 : ℝ)] ![(9823944671759/25000000000000 : ℝ), (26671834164077/50000000000000 : ℝ), (7360552969669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(929613613/2000000000 : ℝ)|^89 ≤ (9823944671759/25000000000000 : ℝ)^73
        have hw : |(929613613/2000000000 : ℝ)|=(929613613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5972368967/10000000000 : ℝ)|^89 ≤ (26671834164077/50000000000000 : ℝ)^73
        have hw : |(5972368967/10000000000 : ℝ)|=(5972368967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1176554193/10000000000 : ℝ)|^89 ≤ (7360552969669/100000000000000 : ℝ)^73
        have hw : |(-1176554193/10000000000 : ℝ)|=(1176554193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c326063_s2_s2_27 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ)) (x : Fin 3 → ℝ) :
    (771014857/1250000000 : ℝ)*x 0 + (744052313/2500000000 : ℝ)*x 1 + (1427850449/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (771014857/1250000000 : ℝ)^89 ≤ (55482856498681/100000000000000 : ℝ)^73 := by
    have hnat : (771014857 : ℕ)^89*100000000000000^73 ≤ 55482856498681^73*1250000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      771014857 1250000000 55482856498681 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (744052313/2500000000 : ℝ)^89 ≤ (22819284844819/100000000000000 : ℝ)^73 := by
    have hnat : (744052313 : ℕ)^89*100000000000000^73 ≤ 22819284844819^73*2500000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      744052313 2500000000 22819284844819 100000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1427850449/5000000000 : ℝ)^89 ≤ (867914345653/4000000000000 : ℝ)^73 := by
    have hnat : (1427850449 : ℕ)^89*4000000000000^73 ≤ 867914345653^73*5000000000^89 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1427850449 5000000000 867914345653 4000000000000 89 73 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (89/16 : ℝ)) 89 73 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(771014857/1250000000 : ℝ), (744052313/2500000000 : ℝ), (1427850449/5000000000 : ℝ)] ![(55482856498681/100000000000000 : ℝ), (22819284844819/100000000000000 : ℝ), (867914345653/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(771014857/1250000000 : ℝ)|^89 ≤ (55482856498681/100000000000000 : ℝ)^73
        have hw : |(771014857/1250000000 : ℝ)|=(771014857/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(744052313/2500000000 : ℝ)|^89 ≤ (22819284844819/100000000000000 : ℝ)^73
        have hw : |(744052313/2500000000 : ℝ)|=(744052313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1427850449/5000000000 : ℝ)|^89 ≤ (867914345653/4000000000000 : ℝ)^73
        have hw : |(1427850449/5000000000 : ℝ)|=(1427850449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c326063_s2 (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((39757/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(39757/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20231/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20231/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38693/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(38693/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3461/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3461/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14057/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14057/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2697/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2697/10000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10213/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10213/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10213/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10213/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10213/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have s2_pow0 : (39757/100000 : ℝ) ^ (87/16 : ℝ) ≤ (132691003077564197/20000000000000000000 : ℝ) := by
    have hpowers : (39757/100000 : ℝ)^87 ≤ (132691003077564197/20000000000000000000 : ℝ)^16 := by
      have hnat : (39757 : ℕ)^87*20000000000000000000^16 ≤ 132691003077564197^16*100000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39757 100000 132691003077564197 20000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39757/100000 : ℝ)) (X := (132691003077564197/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (20132691003077564197/20000000000000000000 : ℝ) ≤ (5006084285877559/5000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (20132691003077564197/20000000000000000000 : ℝ)^16 ≤ (5006084285877559/5000000000000000 : ℝ)^87 := by
      have hnat : (20132691003077564197 : ℕ)^16*5000000000000000^87 ≤ 5006084285877559^87*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20132691003077564197 20000000000000000000 5006084285877559 5000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006084285877559/5000000000000000 : ℝ)) (X := (20132691003077564197/20000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (10132691003077564197/10000000000000000000 : ℝ) ≤ (2004854373448417/2000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (10132691003077564197/10000000000000000000 : ℝ)^16 ≤ (2004854373448417/2000000000000000 : ℝ)^87 := by
      have hnat : (10132691003077564197 : ℕ)^16*2000000000000000^87 ≤ 2004854373448417^87*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10132691003077564197 10000000000000000000 2004854373448417 2000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2004854373448417/2000000000000000 : ℝ)) (X := (10132691003077564197/10000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(6084285877559/1987850000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(12103295486967/3975700000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (39757/100000 : ℝ)) (alpha := (6084285877559/1987850000000000 : ℝ)) (beta := (12103295486967/3975700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (39757/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(6084285877559/1987850000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(12103295486967/3975700000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (20231/50000 : ℝ) ^ (87/16 : ℝ) ≤ (364997547917363961/50000000000000000000 : ℝ) := by
    have hpowers : (20231/50000 : ℝ)^87 ≤ (364997547917363961/50000000000000000000 : ℝ)^16 := by
      have hnat : (20231 : ℕ)^87*50000000000000000000^16 ≤ 364997547917363961^16*50000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20231 50000 364997547917363961 50000000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20231/50000 : ℝ)) (X := (364997547917363961/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (50364997547917363961/50000000000000000000 : ℝ) ≤ (2503346345784323/2500000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (50364997547917363961/50000000000000000000 : ℝ)^16 ≤ (2503346345784323/2500000000000000 : ℝ)^87 := by
      have hnat : (50364997547917363961 : ℕ)^16*2500000000000000^87 ≤ 2503346345784323^87*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50364997547917363961 50000000000000000000 2503346345784323 2500000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503346345784323/2500000000000000 : ℝ)) (X := (50364997547917363961/50000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (25364997547917363961/25000000000000000000 : ℝ) ≤ (10026691834341723/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (25364997547917363961/25000000000000000000 : ℝ)^16 ≤ (10026691834341723/10000000000000000 : ℝ)^87 := by
      have hnat : (25364997547917363961 : ℕ)^16*10000000000000000^87 ≤ 10026691834341723^87*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25364997547917363961 25000000000000000000 10026691834341723 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10026691834341723/10000000000000000 : ℝ)) (X := (25364997547917363961/25000000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(3346345784323/1011550000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(13306451204431/4046200000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (20231/50000 : ℝ)) (alpha := (3346345784323/1011550000000000 : ℝ)) (beta := (13306451204431/4046200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (20231/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(3346345784323/1011550000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(13306451204431/4046200000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (38693/100000 : ℝ) ^ (87/16 : ℝ) ≤ (35779248178571837/6250000000000000000 : ℝ) := by
    have hpowers : (38693/100000 : ℝ)^87 ≤ (35779248178571837/6250000000000000000 : ℝ)^16 := by
      have hnat : (38693 : ℕ)^87*6250000000000000000^16 ≤ 35779248178571837^16*100000^87 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38693 100000 35779248178571837 6250000000000000000 87 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (38693/100000 : ℝ)) (X := (35779248178571837/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (6285779248178571837/6250000000000000000 : ℝ) ≤ (10010503638435979/10000000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (6285779248178571837/6250000000000000000 : ℝ)^16 ≤ (10010503638435979/10000000000000000 : ℝ)^87 := by
      have hnat : (6285779248178571837 : ℕ)^16*10000000000000000^87 ≤ 10010503638435979^87*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6285779248178571837 6250000000000000000 10010503638435979 10000000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10010503638435979/10000000000000000 : ℝ)) (X := (6285779248178571837/6250000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (3160779248178571837/3125000000000000000 : ℝ) ≤ (2505239649348211/2500000000000000 : ℝ) ^ (87/16 : ℝ) := by
    have hpowers : (3160779248178571837/3125000000000000000 : ℝ)^16 ≤ (2505239649348211/2500000000000000 : ℝ)^87 := by
      have hnat : (3160779248178571837 : ℕ)^16*2500000000000000^87 ≤ 2505239649348211^87*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3160779248178571837 3125000000000000000 2505239649348211 2500000000000000 16 87 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2505239649348211/2500000000000000 : ℝ)) (X := (3160779248178571837/3125000000000000000 : ℝ)) (by norm_num) 87 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(10503638435979/3869300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(2090991791373/773860000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (87/16 : ℝ)) (rho := (38693/100000 : ℝ)) (alpha := (10503638435979/3869300000000000 : ℝ)) (beta := (2090991791373/773860000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (38693/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(10503638435979/3869300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(2090991791373/773860000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-50122571/400000000 : ℝ)*X 0 0+(5289294941/10000000000 : ℝ)*X 0 1+(5293883723/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326063_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((661192263/1250000000 : ℝ)*X 1 0+(-125493173/1000000000 : ℝ)*X 1 1+(5292278607/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326063_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((5293223137/10000000000 : ℝ)*X 2 0+(2645930289/5000000000 : ℝ)*X 2 1+(-625225787/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326063_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((2031145361/5000000000 : ℝ)*X 0 0+(2030733789/5000000000 : ℝ)*X 0 1+(1014953217/2500000000 : ℝ)*X 0 2+(2031145361/5000000000 : ℝ)*X 1 0+(2030733789/5000000000 : ℝ)*X 1 1+(1014953217/2500000000 : ℝ)*X 1 2+(2031145361/5000000000 : ℝ)*X 2 0+(2030733789/5000000000 : ℝ)*X 2 1+(1014953217/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326063_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-592378949/5000000000 : ℝ)*X 0 0+(937579993/2000000000 : ℝ)*X 0 1+(1482211503/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326063_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((157890319/312500000 : ℝ)*X 1 0+(-10328097/156250000 : ℝ)*X 1 1+(5927233911/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326063_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((4850735679/10000000000 : ℝ)*X 2 0+(6126687123/10000000000 : ℝ)*X 2 1+(-325454083/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326063_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((4469740269/10000000000 : ℝ)*X 0 0+(5388352577/10000000000 : ℝ)*X 0 1+(270613709/1250000000 : ℝ)*X 0 2+(4469740269/10000000000 : ℝ)*X 1 0+(5388352577/10000000000 : ℝ)*X 1 1+(270613709/1250000000 : ℝ)*X 1 2+(4469740269/10000000000 : ℝ)*X 2 0+(5388352577/10000000000 : ℝ)*X 2 1+(270613709/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326063_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-332297471/5000000000 : ℝ)*X 0 0+(252991621/500000000 : ℝ)*X 0 1+(2958958147/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326063_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((1176157001/2500000000 : ℝ)*X 1 0+(-294995031/2500000000 : ℝ)*X 1 1+(2958151791/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326063_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((5917335273/10000000000 : ℝ)*X 2 0+(5062199589/10000000000 : ℝ)*X 2 1+(-661838133/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326063_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((59791201/100000000 : ℝ)*X 0 0+(3806657417/10000000000 : ℝ)*X 0 1+(43981383/200000000 : ℝ)*X 0 2+(59791201/100000000 : ℝ)*X 1 0+(3806657417/10000000000 : ℝ)*X 1 1+(43981383/200000000 : ℝ)*X 1 2+(59791201/100000000 : ℝ)*X 2 0+(3806657417/10000000000 : ℝ)*X 2 1+(43981383/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326063_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-612253463/10000000000 : ℝ)*X 0 0+(2832692559/5000000000 : ℝ)*X 0 1+(5351383523/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c326063_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((5965760123/10000000000 : ℝ)*X 1 0+(-30482343/500000000 : ℝ)*X 1 1+(1009031577/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c326063_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((929613613/2000000000 : ℝ)*X 2 0+(5972368967/10000000000 : ℝ)*X 2 1+(-1176554193/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c326063_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((771014857/1250000000 : ℝ)*X 0 0+(744052313/2500000000 : ℝ)*X 0 1+(1427850449/5000000000 : ℝ)*X 0 2+(771014857/1250000000 : ℝ)*X 1 0+(744052313/2500000000 : ℝ)*X 1 1+(1427850449/5000000000 : ℝ)*X 1 2+(771014857/1250000000 : ℝ)*X 2 0+(744052313/2500000000 : ℝ)*X 2 1+(1427850449/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c326063_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((3461/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3461/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (18878531017746239896622564012889/3112170338583100000000000000000000000 : ℝ) := by norm_num
    linear_combination (1154941/1000000000000 : ℝ)*(base50) + (83556060411/500000000000 : ℝ)*(base60) + (5362484351247/1000000000000 : ℝ)*(major_s2_0) + (5362484351247/1000000000000 : ℝ)*(major_s2_1) + (5362484351247/1000000000000 : ℝ)*(major_s2_2) + (14596371/1000000000000 : ℝ)*(sp_s2_0) + (3167761/500000000000 : ℝ)*(sp_s2_6) + (4062563853673/500000000000 : ℝ)*(sp_s2_7) + (2031279273777/250000000000 : ℝ)*(sp_s2_8) + (1015639599799/125000000000 : ℝ)*(sp_s2_9) + (2599797000597/1000000000000 : ℝ)*(sp_s2_13) + (5260159/250000000000 : ℝ)*(sp_s2_14) + (9249849/200000000000 : ℝ)*(sp_s2_15) + (46545961/1000000000000 : ℝ)*(sp_s2_23) + (2599803336119/1000000000000 : ℝ)*(f.failure) + (8125163344353/1000000000000 : ℝ)*(f.sum) + (53696582958100003291/78279808300000000000000000000000 : ℝ)*base62 + (161014840424403/154772000000000000000000000 : ℝ)*base65 + (3381155202637077/4046200000000000000000000000 : ℝ)*base67 + (141589758773283/3869300000000000000000000000 : ℝ)*base69 + (105474575601705056603/153831760100000000000000000000000 : ℝ)*base71 + (1851166021944789/3975700000000000000000000000 : ℝ)*base73 + (164415348168731/1011550000000000000000000000 : ℝ)*base75 + (1107460063981993/1987850000000000000000000000 : ℝ)*base77 + (77449592850635785287/160864773400000000000000000000000 : ℝ)*base79 + (22893/20000000000000000 : ℝ)*base86 + (22893/20000000000000000 : ℝ)*base88 + (22893/20000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14057/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14057/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (188517215510131338867304168119/24897362708664800000000000000000000 : ℝ) := by norm_num
    linear_combination (887721/500000000000 : ℝ)*(base60) + (218395867573/40000000000 : ℝ)*(major_s2_0) + (218395867573/40000000000 : ℝ)*(major_s2_1) + (218395867573/40000000000 : ℝ)*(major_s2_2) + (2465289/125000000000 : ℝ)*(sp_s2_0) + (1957553/125000000000 : ℝ)*(sp_s2_1) + (23916859/500000000000 : ℝ)*(sp_s2_2) + (8993179/250000000000 : ℝ)*(sp_s2_7) + (28264773/1000000000000 : ℝ)*(sp_s2_8) + (4136352516859/500000000000 : ℝ)*(sp_s2_14) + (165454336071/20000000000 : ℝ)*(sp_s2_15) + (8272712895029/1000000000000 : ℝ)*(sp_s2_16) + (2646989374761/1000000000000 : ℝ)*(sp_s2_20) + (8150241/200000000000 : ℝ)*(sp_s2_27) + (1323515062983/500000000000 : ℝ)*(f.failure) + (8272760728747/1000000000000 : ℝ)*(f.sum) + (2808010897463144659/15655961660000000000000000000000 : ℝ)*base63 + (804533261543871/773860000000000000000000000 : ℝ)*base65 + (179791428961963/161848000000000000000000000 : ℝ)*base67 + (22249021270003/30954400000000000000000000 : ℝ)*base69 + (2404368846426339249/30766352020000000000000000000000 : ℝ)*base71 + (421553311550201/795140000000000000000000000 : ℝ)*base73 + (70119284291521/101155000000000000000000000 : ℝ)*base75 + (226697445470461/397570000000000000000000000 : ℝ)*base77 + (3326430035987906697/32172954680000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (12301/10000000000000000 : ℝ)*base86 + (12301/10000000000000000 : ℝ)*base88 + (12301/10000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2697/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2697/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (694073207798775873121133049/80432386700000000000000000000000 : ℝ) := by norm_num
    linear_combination (1374469/250000000000 : ℝ)*(base15) + (230489025957/1000000000000 : ℝ)*(base40) + (4993826119467/1000000000000 : ℝ)*(major_s2_0) + (4993826119467/1000000000000 : ℝ)*(major_s2_1) + (4993826119467/1000000000000 : ℝ)*(major_s2_2) + (49699937/1000000000000 : ℝ)*(sp_s2_0) + (56012393/1000000000000 : ℝ)*(sp_s2_1) + (54311503/1000000000000 : ℝ)*(sp_s2_2) + (32723601/1000000000000 : ℝ)*(sp_s2_9) + (1909819/62500000000 : ℝ)*(sp_s2_20) + (7566526712981/1000000000000 : ℝ)*(sp_s2_21) + (945814362831/125000000000 : ℝ)*(sp_s2_22) + (7566489377813/1000000000000 : ℝ)*(sp_s2_23) + (605260598121/250000000000 : ℝ)*(sp_s2_27) + (605268237397/250000000000 : ℝ)*(f.failure) + (7566576412917/1000000000000 : ℝ)*(f.sum) + (12848606395762016371/78279808300000000000000000000000 : ℝ)*base62 + (72233963136771/154772000000000000000000000 : ℝ)*base64 + (1832377170068243/4046200000000000000000000000 : ℝ)*base66 + (360408312552793/3869300000000000000000000000 : ℝ)*base69 + (14973649535321637733/153831760100000000000000000000000 : ℝ)*base71 + (1059868615434321/3975700000000000000000000000 : ℝ)*base72 + (7837277891463/126443750000000000000000000 : ℝ)*base74 + (551429261990313/1987850000000000000000000000 : ℝ)*base77 + (53396112405296996093/160864773400000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (3441/5000000000000000 : ℝ)*base87 + (3441/5000000000000000 : ℝ)*base89 + (3441/5000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (87/16 : ℝ) ≤ p) (hpb : p ≤ (89/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41253/20000 : ℝ) (163929/100000 : ℝ) (10213/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((39757/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(39757/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(20231/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(20231/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(38693/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(38693/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3461/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3461/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14057/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(14057/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2697/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2697/10000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c326063_s2 p hpa hpb X hX hprev1

#print axioms solution
