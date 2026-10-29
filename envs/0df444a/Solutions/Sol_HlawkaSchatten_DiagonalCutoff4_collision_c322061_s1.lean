-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c322061_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:47:25.959283+00:00
-- url     : https://prove2.me/submissions/f35d2d77-9685-4855-b854-d83f386860a1

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
theorem collision_support_c322061_s1_s1_0 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-34879009/200000000 : ℝ)*x 0 + (890228827/2000000000 : ℝ)*x 1 + (588208811/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (34879009/200000000 : ℝ)^83 ≤ (11492326771757/100000000000000 : ℝ)^67 := by
    have hnat : (34879009 : ℕ)^83*100000000000000^67 ≤ 11492326771757^67*200000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34879009 200000000 11492326771757 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (890228827/2000000000 : ℝ)^83 ≤ (18344023375999/50000000000000 : ℝ)^67 := by
    have hnat : (890228827 : ℕ)^83*50000000000000^67 ≤ 18344023375999^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890228827 2000000000 18344023375999 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (588208811/1000000000 : ℝ)^83 ≤ (2590981323097/5000000000000 : ℝ)^67 := by
    have hnat : (588208811 : ℕ)^83*5000000000000^67 ≤ 2590981323097^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      588208811 1000000000 2590981323097 5000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-34879009/200000000 : ℝ), (890228827/2000000000 : ℝ), (588208811/1000000000 : ℝ)] ![(11492326771757/100000000000000 : ℝ), (18344023375999/50000000000000 : ℝ), (2590981323097/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-34879009/200000000 : ℝ)|^83 ≤ (11492326771757/100000000000000 : ℝ)^67
        have hw : |(-34879009/200000000 : ℝ)|=(34879009/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(890228827/2000000000 : ℝ)|^83 ≤ (18344023375999/50000000000000 : ℝ)^67
        have hw : |(890228827/2000000000 : ℝ)|=(890228827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(588208811/1000000000 : ℝ)|^83 ≤ (2590981323097/5000000000000 : ℝ)^67
        have hw : |(588208811/1000000000 : ℝ)|=(588208811/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322061_s1_s1_1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2328292817/5000000000 : ℝ)*x 0 + (-173710739/1000000000 : ℝ)*x 1 + (284660807/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2328292817/5000000000 : ℝ)^83 ≤ (19398589731781/50000000000000 : ℝ)^67 := by
    have hnat : (2328292817 : ℕ)^83*50000000000000^67 ≤ 19398589731781^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2328292817 5000000000 19398589731781 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (173710739/1000000000 : ℝ)^83 ≤ (5718244779297/50000000000000 : ℝ)^67 := by
    have hnat : (173710739 : ℕ)^83*50000000000000^67 ≤ 5718244779297^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173710739 1000000000 5718244779297 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (284660807/500000000 : ℝ)^83 ≤ (49766330956837/100000000000000 : ℝ)^67 := by
    have hnat : (284660807 : ℕ)^83*100000000000000^67 ≤ 49766330956837^67*500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284660807 500000000 49766330956837 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2328292817/5000000000 : ℝ), (-173710739/1000000000 : ℝ), (284660807/500000000 : ℝ)] ![(19398589731781/50000000000000 : ℝ), (5718244779297/50000000000000 : ℝ), (49766330956837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2328292817/5000000000 : ℝ)|^83 ≤ (19398589731781/50000000000000 : ℝ)^67
        have hw : |(2328292817/5000000000 : ℝ)|=(2328292817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-173710739/1000000000 : ℝ)|^83 ≤ (5718244779297/50000000000000 : ℝ)^67
        have hw : |(-173710739/1000000000 : ℝ)|=(173710739/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(284660807/500000000 : ℝ)|^83 ≤ (49766330956837/100000000000000 : ℝ)^67
        have hw : |(284660807/500000000 : ℝ)|=(284660807/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322061_s1_s1_2 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4722522599/10000000000 : ℝ)*x 0 + (1262502361/2000000000 : ℝ)*x 1 + (-369249133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4722522599/10000000000 : ℝ)^83 ≤ (39478883465899/100000000000000 : ℝ)^67 := by
    have hnat : (4722522599 : ℕ)^83*100000000000000^67 ≤ 39478883465899^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4722522599 10000000000 39478883465899 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1262502361/2000000000 : ℝ)^83 ≤ (28278690905319/50000000000000 : ℝ)^67 := by
    have hnat : (1262502361 : ℕ)^83*50000000000000^67 ≤ 28278690905319^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1262502361 2000000000 28278690905319 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (369249133/5000000000 : ℝ)^83 ≤ (792746941719/20000000000000 : ℝ)^67 := by
    have hnat : (369249133 : ℕ)^83*20000000000000^67 ≤ 792746941719^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369249133 5000000000 792746941719 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4722522599/10000000000 : ℝ), (1262502361/2000000000 : ℝ), (-369249133/5000000000 : ℝ)] ![(39478883465899/100000000000000 : ℝ), (28278690905319/50000000000000 : ℝ), (792746941719/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4722522599/10000000000 : ℝ)|^83 ≤ (39478883465899/100000000000000 : ℝ)^67
        have hw : |(4722522599/10000000000 : ℝ)|=(4722522599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1262502361/2000000000 : ℝ)|^83 ≤ (28278690905319/50000000000000 : ℝ)^67
        have hw : |(1262502361/2000000000 : ℝ)|=(1262502361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-369249133/5000000000 : ℝ)|^83 ≤ (792746941719/20000000000000 : ℝ)^67
        have hw : |(-369249133/5000000000 : ℝ)|=(369249133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322061_s1_s1_6 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1300536603/2000000000 : ℝ)*x 0 + (2527364613/10000000000 : ℝ)*x 1 + (766708267/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1300536603/2000000000 : ℝ)^83 ≤ (11735131835233/20000000000000 : ℝ)^67 := by
    have hnat : (1300536603 : ℕ)^83*20000000000000^67 ≤ 11735131835233^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1300536603 2000000000 11735131835233 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2527364613/10000000000 : ℝ)^83 ≤ (18197906480913/100000000000000 : ℝ)^67 := by
    have hnat : (2527364613 : ℕ)^83*100000000000000^67 ≤ 18197906480913^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2527364613 10000000000 18197906480913 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (766708267/2500000000 : ℝ)^83 ≤ (2890804290673/12500000000000 : ℝ)^67 := by
    have hnat : (766708267 : ℕ)^83*12500000000000^67 ≤ 2890804290673^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      766708267 2500000000 2890804290673 12500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1300536603/2000000000 : ℝ), (2527364613/10000000000 : ℝ), (766708267/2500000000 : ℝ)] ![(11735131835233/20000000000000 : ℝ), (18197906480913/100000000000000 : ℝ), (2890804290673/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1300536603/2000000000 : ℝ)|^83 ≤ (11735131835233/20000000000000 : ℝ)^67
        have hw : |(1300536603/2000000000 : ℝ)|=(1300536603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2527364613/10000000000 : ℝ)|^83 ≤ (18197906480913/100000000000000 : ℝ)^67
        have hw : |(2527364613/10000000000 : ℝ)|=(2527364613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(766708267/2500000000 : ℝ)|^83 ≤ (2890804290673/12500000000000 : ℝ)^67
        have hw : |(766708267/2500000000 : ℝ)|=(766708267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322061_s1_s1_7 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-345534599/2000000000 : ℝ)*x 0 + (979627771/2500000000 : ℝ)*x 1 + (1595074757/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (345534599/2000000000 : ℝ)^83 ≤ (11359593992381/100000000000000 : ℝ)^67 := by
    have hnat : (345534599 : ℕ)^83*100000000000000^67 ≤ 11359593992381^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345534599 2000000000 11359593992381 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (979627771/2500000000 : ℝ)^83 ≤ (15664840187359/50000000000000 : ℝ)^67 := by
    have hnat : (979627771 : ℕ)^83*50000000000000^67 ≤ 15664840187359^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979627771 2500000000 15664840187359 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1595074757/2500000000 : ℝ)^83 ≤ (57310725612963/100000000000000 : ℝ)^67 := by
    have hnat : (1595074757 : ℕ)^83*100000000000000^67 ≤ 57310725612963^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1595074757 2500000000 57310725612963 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-345534599/2000000000 : ℝ), (979627771/2500000000 : ℝ), (1595074757/2500000000 : ℝ)] ![(11359593992381/100000000000000 : ℝ), (15664840187359/50000000000000 : ℝ), (57310725612963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-345534599/2000000000 : ℝ)|^83 ≤ (11359593992381/100000000000000 : ℝ)^67
        have hw : |(-345534599/2000000000 : ℝ)|=(345534599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(979627771/2500000000 : ℝ)|^83 ≤ (15664840187359/50000000000000 : ℝ)^67
        have hw : |(979627771/2500000000 : ℝ)|=(979627771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1595074757/2500000000 : ℝ)|^83 ≤ (57310725612963/100000000000000 : ℝ)^67
        have hw : |(1595074757/2500000000 : ℝ)|=(1595074757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322061_s1_s1_8 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4276665059/10000000000 : ℝ)*x 0 + (-628484533/5000000000 : ℝ)*x 1 + (3195279939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4276665059/10000000000 : ℝ)^83 ≤ (174574566107/500000000000 : ℝ)^67 := by
    have hnat : (4276665059 : ℕ)^83*500000000000^67 ≤ 174574566107^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4276665059 10000000000 174574566107 500000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (628484533/5000000000 : ℝ)^83 ≤ (7660161477299/100000000000000 : ℝ)^67 := by
    have hnat : (628484533 : ℕ)^83*100000000000000^67 ≤ 7660161477299^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628484533 5000000000 7660161477299 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3195279939/5000000000 : ℝ)^83 ≤ (57424925284693/100000000000000 : ℝ)^67 := by
    have hnat : (3195279939 : ℕ)^83*100000000000000^67 ≤ 57424925284693^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3195279939 5000000000 57424925284693 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4276665059/10000000000 : ℝ), (-628484533/5000000000 : ℝ), (3195279939/5000000000 : ℝ)] ![(174574566107/500000000000 : ℝ), (7660161477299/100000000000000 : ℝ), (57424925284693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4276665059/10000000000 : ℝ)|^83 ≤ (174574566107/500000000000 : ℝ)^67
        have hw : |(4276665059/10000000000 : ℝ)|=(4276665059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-628484533/5000000000 : ℝ)|^83 ≤ (7660161477299/100000000000000 : ℝ)^67
        have hw : |(-628484533/5000000000 : ℝ)|=(628484533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3195279939/5000000000 : ℝ)|^83 ≤ (57424925284693/100000000000000 : ℝ)^67
        have hw : |(3195279939/5000000000 : ℝ)|=(3195279939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322061_s1_s1_9 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2171595989/5000000000 : ℝ)*x 0 + (698224403/1000000000 : ℝ)*x 1 + (-49448483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171595989/5000000000 : ℝ)^83 ≤ (35588989721029/100000000000000 : ℝ)^67 := by
    have hnat : (2171595989 : ℕ)^83*100000000000000^67 ≤ 35588989721029^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171595989 5000000000 35588989721029 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (698224403/1000000000 : ℝ)^83 ≤ (32041298500359/50000000000000 : ℝ)^67 := by
    have hnat : (698224403 : ℕ)^83*50000000000000^67 ≤ 32041298500359^67*1000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      698224403 1000000000 32041298500359 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (49448483/5000000000 : ℝ)^83 ≤ (65682653251/20000000000000 : ℝ)^67 := by
    have hnat : (49448483 : ℕ)^83*20000000000000^67 ≤ 65682653251^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49448483 5000000000 65682653251 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2171595989/5000000000 : ℝ), (698224403/1000000000 : ℝ), (-49448483/5000000000 : ℝ)] ![(35588989721029/100000000000000 : ℝ), (32041298500359/50000000000000 : ℝ), (65682653251/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2171595989/5000000000 : ℝ)|^83 ≤ (35588989721029/100000000000000 : ℝ)^67
        have hw : |(2171595989/5000000000 : ℝ)|=(2171595989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(698224403/1000000000 : ℝ)|^83 ≤ (32041298500359/50000000000000 : ℝ)^67
        have hw : |(698224403/1000000000 : ℝ)|=(698224403/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-49448483/5000000000 : ℝ)|^83 ≤ (65682653251/20000000000000 : ℝ)^67
        have hw : |(-49448483/5000000000 : ℝ)|=(49448483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322061_s1_s1_13 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1602837721/2500000000 : ℝ)*x 0 + (765867853/2000000000 : ℝ)*x 1 + (358614229/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1602837721/2500000000 : ℝ)^83 ≤ (3603528508219/6250000000000 : ℝ)^67 := by
    have hnat : (1602837721 : ℕ)^83*6250000000000^67 ≤ 3603528508219^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1602837721 2500000000 3603528508219 6250000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (765867853/2000000000 : ℝ)^83 ≤ (30448880534837/100000000000000 : ℝ)^67 := by
    have hnat : (765867853 : ℕ)^83*100000000000000^67 ≤ 30448880534837^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      765867853 2000000000 30448880534837 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (358614229/2000000000 : ℝ)^83 ≤ (743416457489/6250000000000 : ℝ)^67 := by
    have hnat : (358614229 : ℕ)^83*6250000000000^67 ≤ 743416457489^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      358614229 2000000000 743416457489 6250000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1602837721/2500000000 : ℝ), (765867853/2000000000 : ℝ), (358614229/2000000000 : ℝ)] ![(3603528508219/6250000000000 : ℝ), (30448880534837/100000000000000 : ℝ), (743416457489/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1602837721/2500000000 : ℝ)|^83 ≤ (3603528508219/6250000000000 : ℝ)^67
        have hw : |(1602837721/2500000000 : ℝ)|=(1602837721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(765867853/2000000000 : ℝ)|^83 ≤ (30448880534837/100000000000000 : ℝ)^67
        have hw : |(765867853/2000000000 : ℝ)|=(765867853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(358614229/2000000000 : ℝ)|^83 ≤ (743416457489/6250000000000 : ℝ)^67
        have hw : |(358614229/2000000000 : ℝ)|=(358614229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322061_s1_s1_14 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-208589473/2500000000 : ℝ)*x 0 + (4592605761/10000000000 : ℝ)*x 1 + (398435509/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (208589473/2500000000 : ℝ)^83 ≤ (4610678991017/100000000000000 : ℝ)^67 := by
    have hnat : (208589473 : ℕ)^83*100000000000000^67 ≤ 4610678991017^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208589473 2500000000 4610678991017 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4592605761/10000000000 : ℝ)^83 ≤ (38137908952001/100000000000000 : ℝ)^67 := by
    have hnat : (4592605761 : ℕ)^83*100000000000000^67 ≤ 38137908952001^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4592605761 10000000000 38137908952001 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (398435509/625000000 : ℝ)^83 ≤ (5725141204391/10000000000000 : ℝ)^67 := by
    have hnat : (398435509 : ℕ)^83*10000000000000^67 ≤ 5725141204391^67*625000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398435509 625000000 5725141204391 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-208589473/2500000000 : ℝ), (4592605761/10000000000 : ℝ), (398435509/625000000 : ℝ)] ![(4610678991017/100000000000000 : ℝ), (38137908952001/100000000000000 : ℝ), (5725141204391/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-208589473/2500000000 : ℝ)|^83 ≤ (4610678991017/100000000000000 : ℝ)^67
        have hw : |(-208589473/2500000000 : ℝ)|=(208589473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4592605761/10000000000 : ℝ)|^83 ≤ (38137908952001/100000000000000 : ℝ)^67
        have hw : |(4592605761/10000000000 : ℝ)|=(4592605761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(398435509/625000000 : ℝ)|^83 ≤ (5725141204391/10000000000000 : ℝ)^67
        have hw : |(398435509/625000000 : ℝ)|=(398435509/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322061_s1_s1_15 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (853840771/2000000000 : ℝ)*x 0 + (-1274794373/10000000000 : ℝ)*x 1 + (3192613693/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (853840771/2000000000 : ℝ)^83 ≤ (17419734375573/50000000000000 : ℝ)^67 := by
    have hnat : (853840771 : ℕ)^83*50000000000000^67 ≤ 17419734375573^67*2000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853840771 2000000000 17419734375573 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1274794373/10000000000 : ℝ)^83 ≤ (3897480099833/50000000000000 : ℝ)^67 := by
    have hnat : (1274794373 : ℕ)^83*50000000000000^67 ≤ 3897480099833^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1274794373 10000000000 3897480099833 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3192613693/5000000000 : ℝ)^83 ≤ (11473114208871/20000000000000 : ℝ)^67 := by
    have hnat : (3192613693 : ℕ)^83*20000000000000^67 ≤ 11473114208871^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3192613693 5000000000 11473114208871 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(853840771/2000000000 : ℝ), (-1274794373/10000000000 : ℝ), (3192613693/5000000000 : ℝ)] ![(17419734375573/50000000000000 : ℝ), (3897480099833/50000000000000 : ℝ), (11473114208871/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(853840771/2000000000 : ℝ)|^83 ≤ (17419734375573/50000000000000 : ℝ)^67
        have hw : |(853840771/2000000000 : ℝ)|=(853840771/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1274794373/10000000000 : ℝ)|^83 ≤ (3897480099833/50000000000000 : ℝ)^67
        have hw : |(-1274794373/10000000000 : ℝ)|=(1274794373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3192613693/5000000000 : ℝ)|^83 ≤ (11473114208871/20000000000000 : ℝ)^67
        have hw : |(3192613693/5000000000 : ℝ)|=(3192613693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322061_s1_s1_16 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2845086213/5000000000 : ℝ)*x 0 + (713380823/1250000000 : ℝ)*x 1 + (-1628569/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2845086213/5000000000 : ℝ)^83 ≤ (9946674644403/20000000000000 : ℝ)^67 := by
    have hnat : (2845086213 : ℕ)^83*20000000000000^67 ≤ 9946674644403^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2845086213 5000000000 9946674644403 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (713380823/1250000000 : ℝ)^83 ≤ (49916141797487/100000000000000 : ℝ)^67 := by
    have hnat : (713380823 : ℕ)^83*100000000000000^67 ≤ 49916141797487^67*1250000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      713380823 1250000000 49916141797487 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1628569/156250000 : ℝ)^83 ≤ (175242483293/50000000000000 : ℝ)^67 := by
    have hnat : (1628569 : ℕ)^83*50000000000000^67 ≤ 175242483293^67*156250000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1628569 156250000 175242483293 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2845086213/5000000000 : ℝ), (713380823/1250000000 : ℝ), (-1628569/156250000 : ℝ)] ![(9946674644403/20000000000000 : ℝ), (49916141797487/100000000000000 : ℝ), (175242483293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2845086213/5000000000 : ℝ)|^83 ≤ (9946674644403/20000000000000 : ℝ)^67
        have hw : |(2845086213/5000000000 : ℝ)|=(2845086213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(713380823/1250000000 : ℝ)|^83 ≤ (49916141797487/100000000000000 : ℝ)^67
        have hw : |(713380823/1250000000 : ℝ)|=(713380823/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1628569/156250000 : ℝ)|^83 ≤ (175242483293/50000000000000 : ℝ)^67
        have hw : |(-1628569/156250000 : ℝ)|=(1628569/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322061_s1_s1_20 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7730082751/10000000000 : ℝ)*x 0 + (1097918989/5000000000 : ℝ)*x 1 + (904159811/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7730082751/10000000000 : ℝ)^83 ≤ (72691201769741/100000000000000 : ℝ)^67 := by
    have hnat : (7730082751 : ℕ)^83*100000000000000^67 ≤ 72691201769741^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7730082751 10000000000 72691201769741 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097918989/5000000000 : ℝ)^83 ≤ (7644349159919/50000000000000 : ℝ)^67 := by
    have hnat : (1097918989 : ℕ)^83*50000000000000^67 ≤ 7644349159919^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097918989 5000000000 7644349159919 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (904159811/5000000000 : ℝ)^83 ≤ (6010049950649/50000000000000 : ℝ)^67 := by
    have hnat : (904159811 : ℕ)^83*50000000000000^67 ≤ 6010049950649^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      904159811 5000000000 6010049950649 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7730082751/10000000000 : ℝ), (1097918989/5000000000 : ℝ), (904159811/5000000000 : ℝ)] ![(72691201769741/100000000000000 : ℝ), (7644349159919/50000000000000 : ℝ), (6010049950649/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7730082751/10000000000 : ℝ)|^83 ≤ (72691201769741/100000000000000 : ℝ)^67
        have hw : |(7730082751/10000000000 : ℝ)|=(7730082751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1097918989/5000000000 : ℝ)|^83 ≤ (7644349159919/50000000000000 : ℝ)^67
        have hw : |(1097918989/5000000000 : ℝ)|=(1097918989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(904159811/5000000000 : ℝ)|^83 ≤ (6010049950649/50000000000000 : ℝ)^67
        have hw : |(904159811/5000000000 : ℝ)|=(904159811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322061_s1_s1_21 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-749885367/10000000000 : ℝ)*x 0 + (5254414437/10000000000 : ℝ)*x 1 + (115955723/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (749885367/10000000000 : ℝ)^83 ≤ (807917351199/20000000000000 : ℝ)^67 := by
    have hnat : (749885367 : ℕ)^83*20000000000000^67 ≤ 807917351199^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      749885367 10000000000 807917351199 20000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5254414437/10000000000 : ℝ)^83 ≤ (22529620112921/50000000000000 : ℝ)^67 := by
    have hnat : (5254414437 : ℕ)^83*50000000000000^67 ≤ 22529620112921^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254414437 10000000000 22529620112921 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (115955723/200000000 : ℝ)^83 ≤ (50901173005187/100000000000000 : ℝ)^67 := by
    have hnat : (115955723 : ℕ)^83*100000000000000^67 ≤ 50901173005187^67*200000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115955723 200000000 50901173005187 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-749885367/10000000000 : ℝ), (5254414437/10000000000 : ℝ), (115955723/200000000 : ℝ)] ![(807917351199/20000000000000 : ℝ), (22529620112921/50000000000000 : ℝ), (50901173005187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-749885367/10000000000 : ℝ)|^83 ≤ (807917351199/20000000000000 : ℝ)^67
        have hw : |(-749885367/10000000000 : ℝ)|=(749885367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5254414437/10000000000 : ℝ)|^83 ≤ (22529620112921/50000000000000 : ℝ)^67
        have hw : |(5254414437/10000000000 : ℝ)|=(5254414437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(115955723/200000000 : ℝ)|^83 ≤ (50901173005187/100000000000000 : ℝ)^67
        have hw : |(115955723/200000000 : ℝ)|=(115955723/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322061_s1_s1_22 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5708117851/10000000000 : ℝ)*x 0 + (-368214501/5000000000 : ℝ)*x 1 + (5354254091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5708117851/10000000000 : ℝ)^83 ≤ (49927749341579/100000000000000 : ℝ)^67 := by
    have hnat : (5708117851 : ℕ)^83*100000000000000^67 ≤ 49927749341579^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5708117851 10000000000 49927749341579 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (368214501/5000000000 : ℝ)^83 ≤ (1974990356773/50000000000000 : ℝ)^67 := by
    have hnat : (368214501 : ℕ)^83*50000000000000^67 ≤ 1974990356773^67*5000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368214501 5000000000 1974990356773 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5354254091/10000000000 : ℝ)^83 ≤ (46122269936311/100000000000000 : ℝ)^67 := by
    have hnat : (5354254091 : ℕ)^83*100000000000000^67 ≤ 46122269936311^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354254091 10000000000 46122269936311 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5708117851/10000000000 : ℝ), (-368214501/5000000000 : ℝ), (5354254091/10000000000 : ℝ)] ![(49927749341579/100000000000000 : ℝ), (1974990356773/50000000000000 : ℝ), (46122269936311/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5708117851/10000000000 : ℝ)|^83 ≤ (49927749341579/100000000000000 : ℝ)^67
        have hw : |(5708117851/10000000000 : ℝ)|=(5708117851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-368214501/5000000000 : ℝ)|^83 ≤ (1974990356773/50000000000000 : ℝ)^67
        have hw : |(-368214501/5000000000 : ℝ)|=(368214501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5354254091/10000000000 : ℝ)|^83 ≤ (46122269936311/100000000000000 : ℝ)^67
        have hw : |(5354254091/10000000000 : ℝ)|=(5354254091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322061_s1_s1_23 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1040900521/2500000000 : ℝ)*x 0 + (6944345999/10000000000 : ℝ)*x 1 + (-521019281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1040900521/2500000000 : ℝ)^83 ≤ (3377506507771/10000000000000 : ℝ)^67 := by
    have hnat : (1040900521 : ℕ)^83*10000000000000^67 ≤ 3377506507771^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040900521 2500000000 3377506507771 10000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6944345999/10000000000 : ℝ)^83 ≤ (63651988029437/100000000000000 : ℝ)^67 := by
    have hnat : (6944345999 : ℕ)^83*100000000000000^67 ≤ 63651988029437^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6944345999 10000000000 63651988029437 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (521019281/10000000000 : ℝ)^83 ≤ (1286473442729/50000000000000 : ℝ)^67 := by
    have hnat : (521019281 : ℕ)^83*50000000000000^67 ≤ 1286473442729^67*10000000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521019281 10000000000 1286473442729 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1040900521/2500000000 : ℝ), (6944345999/10000000000 : ℝ), (-521019281/10000000000 : ℝ)] ![(3377506507771/10000000000000 : ℝ), (63651988029437/100000000000000 : ℝ), (1286473442729/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1040900521/2500000000 : ℝ)|^83 ≤ (3377506507771/10000000000000 : ℝ)^67
        have hw : |(1040900521/2500000000 : ℝ)|=(1040900521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6944345999/10000000000 : ℝ)|^83 ≤ (63651988029437/100000000000000 : ℝ)^67
        have hw : |(6944345999/10000000000 : ℝ)|=(6944345999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-521019281/10000000000 : ℝ)|^83 ≤ (1286473442729/50000000000000 : ℝ)^67
        have hw : |(-521019281/10000000000 : ℝ)|=(521019281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c322061_s1_s1_27 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2055583249/2500000000 : ℝ)*x 0 + (2007431/12500000 : ℝ)*x 1 + (425625049/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2055583249/2500000000 : ℝ)^83 ≤ (19617126069783/25000000000000 : ℝ)^67 := by
    have hnat : (2055583249 : ℕ)^83*25000000000000^67 ≤ 19617126069783^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055583249 2500000000 19617126069783 25000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2007431/12500000 : ℝ)^83 ≤ (10376582470827/100000000000000 : ℝ)^67 := by
    have hnat : (2007431 : ℕ)^83*100000000000000^67 ≤ 10376582470827^67*12500000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2007431 12500000 10376582470827 100000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (425625049/2500000000 : ℝ)^83 ≤ (5577456614731/50000000000000 : ℝ)^67 := by
    have hnat : (425625049 : ℕ)^83*50000000000000^67 ≤ 5577456614731^67*2500000000^83 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425625049 2500000000 5577456614731 50000000000000 83 67 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (83/16 : ℝ)) 83 67 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2055583249/2500000000 : ℝ), (2007431/12500000 : ℝ), (425625049/2500000000 : ℝ)] ![(19617126069783/25000000000000 : ℝ), (10376582470827/100000000000000 : ℝ), (5577456614731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2055583249/2500000000 : ℝ)|^83 ≤ (19617126069783/25000000000000 : ℝ)^67
        have hw : |(2055583249/2500000000 : ℝ)|=(2055583249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2007431/12500000 : ℝ)|^83 ≤ (10376582470827/100000000000000 : ℝ)^67
        have hw : |(2007431/12500000 : ℝ)|=(2007431/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(425625049/2500000000 : ℝ)|^83 ≤ (5577456614731/50000000000000 : ℝ)^67
        have hw : |(425625049/2500000000 : ℝ)|=(425625049/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c322061_s1 (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((71209/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(71209/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35187/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(35187/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(65793/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(65793/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((17873/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17873/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(42619/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(42619/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9531/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(9531/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2522/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2522/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2522/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2522/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2522/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (71209/100000 : ℝ) ^ (41/8 : ℝ) ≤ (17548552349195714409/100000000000000000000 : ℝ) := by
    have hpowers : (71209/100000 : ℝ)^41 ≤ (17548552349195714409/100000000000000000000 : ℝ)^8 := by
      have hnat : (71209 : ℕ)^41*100000000000000000000^8 ≤ 17548552349195714409^8*100000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71209 100000 17548552349195714409 100000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (71209/100000 : ℝ)) (X := (17548552349195714409/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (117548552349195714409/100000000000000000000 : ℝ) ≤ (5160252322669193/5000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (117548552349195714409/100000000000000000000 : ℝ)^8 ≤ (5160252322669193/5000000000000000 : ℝ)^41 := by
      have hnat : (117548552349195714409 : ℕ)^8*5000000000000000^41 ≤ 5160252322669193^41*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        117548552349195714409 100000000000000000000 5160252322669193 5000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5160252322669193/5000000000000000 : ℝ)) (X := (117548552349195714409/100000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (67548552349195714409/50000000000000000000 : ℝ) ≤ (10604541855177143/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (67548552349195714409/50000000000000000000 : ℝ)^8 ≤ (10604541855177143/10000000000000000 : ℝ)^41 := by
      have hnat : (67548552349195714409 : ℕ)^8*10000000000000000^41 ≤ 10604541855177143^41*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67548552349195714409 50000000000000000000 10604541855177143 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10604541855177143/10000000000000000 : ℝ)) (X := (67548552349195714409/50000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(160252322669193/3560450000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(284037209838757/7120900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (71209/100000 : ℝ)) (alpha := (160252322669193/3560450000000000 : ℝ)) (beta := (284037209838757/7120900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (71209/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(160252322669193/3560450000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(284037209838757/7120900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (35187/50000 : ℝ) ^ (41/8 : ℝ) ≤ (516223456728072889/3125000000000000000 : ℝ) := by
    have hpowers : (35187/50000 : ℝ)^41 ≤ (516223456728072889/3125000000000000000 : ℝ)^8 := by
      have hnat : (35187 : ℕ)^41*3125000000000000000^8 ≤ 516223456728072889^8*50000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35187 50000 516223456728072889 3125000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (35187/50000 : ℝ)) (X := (516223456728072889/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (3641223456728072889/3125000000000000000 : ℝ) ≤ (2575701799439427/2500000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (3641223456728072889/3125000000000000000 : ℝ)^8 ≤ (2575701799439427/2500000000000000 : ℝ)^41 := by
      have hnat : (3641223456728072889 : ℕ)^8*2500000000000000^41 ≤ 2575701799439427^41*3125000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3641223456728072889 3125000000000000000 2575701799439427 2500000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2575701799439427/2500000000000000 : ℝ)) (X := (3641223456728072889/3125000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (2078723456728072889/1562500000000000000 : ℝ) ≤ (2114562711194603/2000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (2078723456728072889/1562500000000000000 : ℝ)^8 ≤ (2114562711194603/2000000000000000 : ℝ)^41 := by
      have hnat : (2078723456728072889 : ℕ)^8*2000000000000000^41 ≤ 2114562711194603^41*1562500000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2078723456728072889 1562500000000000000 2114562711194603 2000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2114562711194603/2000000000000000 : ℝ)) (X := (2078723456728072889/1562500000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(75701799439427/1759350000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(270006358215307/7037400000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (35187/50000 : ℝ)) (alpha := (75701799439427/1759350000000000 : ℝ)) (beta := (270006358215307/7037400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (35187/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(75701799439427/1759350000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(270006358215307/7037400000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (65793/100000 : ℝ) ^ (41/8 : ℝ) ≤ (1169959718382586779/10000000000000000000 : ℝ) := by
    have hpowers : (65793/100000 : ℝ)^41 ≤ (1169959718382586779/10000000000000000000 : ℝ)^8 := by
      have hnat : (65793 : ℕ)^41*10000000000000000000^8 ≤ 1169959718382586779^8*100000^41 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65793 100000 1169959718382586779 10000000000000000000 41 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (65793/100000 : ℝ)) (X := (1169959718382586779/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (11169959718382586779/10000000000000000000 : ℝ) ≤ (10218235868127737/10000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (11169959718382586779/10000000000000000000 : ℝ)^8 ≤ (10218235868127737/10000000000000000 : ℝ)^41 := by
      have hnat : (11169959718382586779 : ℕ)^8*10000000000000000^41 ≤ 10218235868127737^41*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11169959718382586779 10000000000000000000 10218235868127737 10000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10218235868127737/10000000000000000 : ℝ)) (X := (11169959718382586779/10000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (6169959718382586779/5000000000000000000 : ℝ) ≤ (5209392053648041/5000000000000000 : ℝ) ^ (41/8 : ℝ) := by
    have hpowers : (6169959718382586779/5000000000000000000 : ℝ)^8 ≤ (5209392053648041/5000000000000000 : ℝ)^41 := by
      have hnat : (6169959718382586779 : ℕ)^8*5000000000000000^41 ≤ 5209392053648041^41*5000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6169959718382586779 5000000000000000000 5209392053648041 5000000000000000 8 41 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5209392053648041/5000000000000000 : ℝ)) (X := (6169959718382586779/5000000000000000000 : ℝ)) (by norm_num) 41 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(218235868127737/6579300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(13369882611223/438620000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (41/8 : ℝ)) (rho := (65793/100000 : ℝ)) (alpha := (218235868127737/6579300000000000 : ℝ)) (beta := (13369882611223/438620000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (65793/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(218235868127737/6579300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(13369882611223/438620000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-34879009/200000000 : ℝ)*X 0 0+(890228827/2000000000 : ℝ)*X 0 1+(588208811/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322061_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2328292817/5000000000 : ℝ)*X 1 0+(-173710739/1000000000 : ℝ)*X 1 1+(284660807/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322061_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((4722522599/10000000000 : ℝ)*X 2 0+(1262502361/2000000000 : ℝ)*X 2 1+(-369249133/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322061_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((1300536603/2000000000 : ℝ)*X 0 0+(2527364613/10000000000 : ℝ)*X 0 1+(766708267/2500000000 : ℝ)*X 0 2+(1300536603/2000000000 : ℝ)*X 1 0+(2527364613/10000000000 : ℝ)*X 1 1+(766708267/2500000000 : ℝ)*X 1 2+(1300536603/2000000000 : ℝ)*X 2 0+(2527364613/10000000000 : ℝ)*X 2 1+(766708267/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322061_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-345534599/2000000000 : ℝ)*X 0 0+(979627771/2500000000 : ℝ)*X 0 1+(1595074757/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322061_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((4276665059/10000000000 : ℝ)*X 1 0+(-628484533/5000000000 : ℝ)*X 1 1+(3195279939/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322061_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((2171595989/5000000000 : ℝ)*X 2 0+(698224403/1000000000 : ℝ)*X 2 1+(-49448483/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322061_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((1602837721/2500000000 : ℝ)*X 0 0+(765867853/2000000000 : ℝ)*X 0 1+(358614229/2000000000 : ℝ)*X 0 2+(1602837721/2500000000 : ℝ)*X 1 0+(765867853/2000000000 : ℝ)*X 1 1+(358614229/2000000000 : ℝ)*X 1 2+(1602837721/2500000000 : ℝ)*X 2 0+(765867853/2000000000 : ℝ)*X 2 1+(358614229/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322061_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-208589473/2500000000 : ℝ)*X 0 0+(4592605761/10000000000 : ℝ)*X 0 1+(398435509/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322061_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((853840771/2000000000 : ℝ)*X 1 0+(-1274794373/10000000000 : ℝ)*X 1 1+(3192613693/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322061_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((2845086213/5000000000 : ℝ)*X 2 0+(713380823/1250000000 : ℝ)*X 2 1+(-1628569/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322061_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((7730082751/10000000000 : ℝ)*X 0 0+(1097918989/5000000000 : ℝ)*X 0 1+(904159811/5000000000 : ℝ)*X 0 2+(7730082751/10000000000 : ℝ)*X 1 0+(1097918989/5000000000 : ℝ)*X 1 1+(904159811/5000000000 : ℝ)*X 1 2+(7730082751/10000000000 : ℝ)*X 2 0+(1097918989/5000000000 : ℝ)*X 2 1+(904159811/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322061_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-749885367/10000000000 : ℝ)*X 0 0+(5254414437/10000000000 : ℝ)*X 0 1+(115955723/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c322061_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((5708117851/10000000000 : ℝ)*X 1 0+(-368214501/5000000000 : ℝ)*X 1 1+(5354254091/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c322061_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((1040900521/2500000000 : ℝ)*X 2 0+(6944345999/10000000000 : ℝ)*X 2 1+(-521019281/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c322061_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((2055583249/2500000000 : ℝ)*X 0 0+(2007431/12500000 : ℝ)*X 0 1+(425625049/2500000000 : ℝ)*X 0 2+(2055583249/2500000000 : ℝ)*X 1 0+(2007431/12500000 : ℝ)*X 1 1+(425625049/2500000000 : ℝ)*X 1 2+(2055583249/2500000000 : ℝ)*X 2 0+(2007431/12500000 : ℝ)*X 2 1+(425625049/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c322061_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((17873/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17873/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (659906893333614591459163/73493914000000000000000000000 : ℝ) := by norm_num
    linear_combination (26647/500000000000 : ℝ)*(base23) + (197/312500000 : ℝ)*(base50) + (31643800061/31250000000 : ℝ)*(base59) + (53172488089/10000000000 : ℝ)*(major_s1_0) + (53172488089/10000000000 : ℝ)*(major_s1_1) + (53172488089/10000000000 : ℝ)*(major_s1_2) + (46284113/1000000000000 : ℝ)*(sp_s1_0) + (30521859/1000000000000 : ℝ)*(sp_s1_6) + (1969813597043/250000000000 : ℝ)*(sp_s1_7) + (3938015933533/500000000000 : ℝ)*(sp_s1_8) + (7879198927271/1000000000000 : ℝ)*(sp_s1_9) + (1377581715313/500000000000 : ℝ)*(sp_s1_13) + (163440261/50000000000 : ℝ)*(sp_s1_15) + (101691721/1000000000000 : ℝ)*(sp_s1_23) + (551038790497/200000000000 : ℝ)*(f.failure) + (1575860134457/200000000000 : ℝ)*(f.sum) + (197680145089630773/367469570000000000000000000000 : ℝ)*base62 + (325055193033/3133000000000000000000000 : ℝ)*base64 + (78165776600579/351870000000000000000000000 : ℝ)*base67 + (65564108025947/93990000000000000000000000 : ℝ)*base68 + (102871068095980693/2230977970000000000000000000000 : ℝ)*base71 + (12249454854593/17802250000000000000000000 : ℝ)*base72 + (350114614159817/351870000000000000000000000 : ℝ)*base74 + (289369570806227/356045000000000000000000000 : ℝ)*base76 + (298492237057813903/1252815541500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (1603/2000000000000000 : ℝ)*base87 + (1603/2000000000000000 : ℝ)*base89 + (1603/2000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(42619/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(42619/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2070069577109461724463540832139/130835703050650000000000000000000000 : ℝ) := by norm_num
    linear_combination (3207293/1000000000000 : ℝ)*(base19) + (59061/500000000000 : ℝ)*(base21) + (8331101/1000000000000 : ℝ)*(base53) + (3573473637/8000000000 : ℝ)*(base59) + (249119146401/50000000000 : ℝ)*(major_s1_0) + (249119146401/50000000000 : ℝ)*(major_s1_1) + (4982374596919/1000000000000 : ℝ)*(major_s1_2) + (1390233/125000000000 : ℝ)*(sp_s1_6) + (22877217/500000000000 : ℝ)*(sp_s1_7) + (3691513586103/500000000000 : ℝ)*(sp_s1_14) + (7383069719347/1000000000000 : ℝ)*(sp_s1_15) + (3691540569809/500000000000 : ℝ)*(sp_s1_16) + (2581514311783/1000000000000 : ℝ)*(sp_s1_20) + (153890681/1000000000000 : ℝ)*(sp_s1_27) + (322709915541/125000000000 : ℝ)*(f.failure) + (7383081257741/1000000000000 : ℝ)*(f.sum) + (17867207302745951023/77168609700000000000000000000000 : ℝ)*base62 + (103293465068873/438620000000000000000000000 : ℝ)*base64 + (61700766913661/117290000000000000000000000 : ℝ)*base66 + (1986468175932917/6579300000000000000000000000 : ℝ)*base68 + (6003172871678492219/31233691580000000000000000000000 : ℝ)*base70 + (7518125583297/14241800000000000000000000 : ℝ)*base72 + (17425804109163/117290000000000000000000000 : ℝ)*base75 + (5692587349191/71209000000000000000000000 : ℝ)*base77 + (476195264882519699/8352103610000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (759/1250000000000000 : ℝ)*base87 + (759/1250000000000000 : ℝ)*base89 + (759/1250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9531/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(9531/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (107850053655012021612907071453/13083570305065000000000000000000000 : ℝ) := by norm_num
    linear_combination (4333161/500000000000 : ℝ)*(base11) + (5799151/1000000000000 : ℝ)*(base15) + (28167420857/100000000000 : ℝ)*(base40) + (112767726349/250000000000 : ℝ)*(base59) + (167552847689/40000000000 : ℝ)*(major_s1_0) + (167552847689/40000000000 : ℝ)*(major_s1_1) + (167552847689/40000000000 : ℝ)*(major_s1_2) + (641351/500000000000 : ℝ)*(sp_s1_1) + (355727/62500000000 : ℝ)*(sp_s1_2) + (12963679/250000000000 : ℝ)*(sp_s1_9) + (24828579341/4000000000 : ℝ)*(sp_s1_21) + (6207146419719/1000000000000 : ℝ)*(sp_s1_22) + (775886994403/125000000000 : ℝ)*(sp_s1_23) + (2170486135149/1000000000000 : ℝ)*(sp_s1_27) + (2170486135149/1000000000000 : ℝ)*(f.failure) + (1551788375393/250000000000 : ℝ)*(f.sum) + (2088976563583896513/5144573980000000000000000000000 : ℝ)*base63 + (4453243096917/17544800000000000000000000 : ℝ)*base65 + (81087250656977/1407480000000000000000000000 : ℝ)*base66 + (591361386540139/1315860000000000000000000000 : ℝ)*base69 + (7069057216046334139/31233691580000000000000000000000 : ℝ)*base71 + (117154259556769/1424180000000000000000000000 : ℝ)*base72 + (121198840603283/351870000000000000000000000 : ℝ)*base75 + (40554895878741/712090000000000000000000000 : ℝ)*base77 + (9928894614701960701/100225243320000000000000000000000 : ℝ)*base79 + (9449/10000000000000000 : ℝ)*base86 + (9449/10000000000000000 : ℝ)*base88 + (9449/10000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (41/8 : ℝ) ≤ p) (hpb : p ≤ (83/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19299/10000 : ℝ) (167697/100000 : ℝ) (2522/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((71209/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(71209/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(35187/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(35187/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(65793/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(65793/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((17873/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17873/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(42619/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(42619/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(9531/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(9531/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c322061_s1 p hpa hpb X hX hprev0

#print axioms solution
