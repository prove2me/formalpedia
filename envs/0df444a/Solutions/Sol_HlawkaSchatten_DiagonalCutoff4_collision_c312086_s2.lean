-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c312086_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:22:16.439429+00:00
-- url     : https://prove2.me/submissions/8074b69b-cac6-4349-b46e-f99379e534cf

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
theorem collision_support_c312086_s2_s2_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1000679623/10000000000 : ℝ)*x 0 + (-1127918003/2000000000 : ℝ)*x 1 + (1380369687/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1000679623/10000000000 : ℝ)^73 ≤ (5244162307451/100000000000000 : ℝ)^57 := by
    have hnat : (1000679623 : ℕ)^73*100000000000000^57 ≤ 5244162307451^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000679623 10000000000 5244162307451 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1127918003/2000000000 : ℝ)^73 ≤ (48020013633853/100000000000000 : ℝ)^57 := by
    have hnat : (1127918003 : ℕ)^73*100000000000000^57 ≤ 48020013633853^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127918003 2000000000 48020013633853 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1380369687/2500000000 : ℝ)^73 ≤ (46735824043103/100000000000000 : ℝ)^57 := by
    have hnat : (1380369687 : ℕ)^73*100000000000000^57 ≤ 46735824043103^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380369687 2500000000 46735824043103 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1000679623/10000000000 : ℝ), (-1127918003/2000000000 : ℝ), (1380369687/2500000000 : ℝ)] ![(5244162307451/100000000000000 : ℝ), (48020013633853/100000000000000 : ℝ), (46735824043103/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1000679623/10000000000 : ℝ)|^73 ≤ (5244162307451/100000000000000 : ℝ)^57
        have hw : |(-1000679623/10000000000 : ℝ)|=(1000679623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1127918003/2000000000 : ℝ)|^73 ≤ (48020013633853/100000000000000 : ℝ)^57
        have hw : |(-1127918003/2000000000 : ℝ)|=(1127918003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1380369687/2500000000 : ℝ)|^73 ≤ (46735824043103/100000000000000 : ℝ)^57
        have hw : |(1380369687/2500000000 : ℝ)|=(1380369687/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312086_s2_s2_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5801951057/10000000000 : ℝ)*x 0 + (436922353/1250000000 : ℝ)*x 1 + (1650267161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5801951057/10000000000 : ℝ)^73 ≤ (9959530839497/20000000000000 : ℝ)^57 := by
    have hnat : (5801951057 : ℕ)^73*20000000000000^57 ≤ 9959530839497^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5801951057 10000000000 9959530839497 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (436922353/1250000000 : ℝ)^73 ≤ (2602269587239/10000000000000 : ℝ)^57 := by
    have hnat : (436922353 : ℕ)^73*10000000000000^57 ≤ 2602269587239^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436922353 1250000000 2602269587239 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1650267161/5000000000 : ℝ)^73 ≤ (6044912478483/25000000000000 : ℝ)^57 := by
    have hnat : (1650267161 : ℕ)^73*25000000000000^57 ≤ 6044912478483^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1650267161 5000000000 6044912478483 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5801951057/10000000000 : ℝ), (436922353/1250000000 : ℝ), (1650267161/5000000000 : ℝ)] ![(9959530839497/20000000000000 : ℝ), (2602269587239/10000000000000 : ℝ), (6044912478483/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5801951057/10000000000 : ℝ)|^73 ≤ (9959530839497/20000000000000 : ℝ)^57
        have hw : |(5801951057/10000000000 : ℝ)|=(5801951057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(436922353/1250000000 : ℝ)|^73 ≤ (2602269587239/10000000000000 : ℝ)^57
        have hw : |(436922353/1250000000 : ℝ)|=(436922353/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1650267161/5000000000 : ℝ)|^73 ≤ (6044912478483/25000000000000 : ℝ)^57
        have hw : |(1650267161/5000000000 : ℝ)|=(1650267161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312086_s2_s2_6 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4614834163/10000000000 : ℝ)*x 0 + (-3415733063/10000000000 : ℝ)*x 1 + (4658144957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4614834163/10000000000 : ℝ)^73 ≤ (37143611376919/100000000000000 : ℝ)^57 := by
    have hnat : (4614834163 : ℕ)^73*100000000000000^57 ≤ 37143611376919^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4614834163 10000000000 37143611376919 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3415733063/10000000000 : ℝ)^73 ≤ (25265741150401/100000000000000 : ℝ)^57 := by
    have hnat : (3415733063 : ℕ)^73*100000000000000^57 ≤ 25265741150401^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3415733063 10000000000 25265741150401 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4658144957/10000000000 : ℝ)^73 ≤ (37590647458991/100000000000000 : ℝ)^57 := by
    have hnat : (4658144957 : ℕ)^73*100000000000000^57 ≤ 37590647458991^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4658144957 10000000000 37590647458991 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4614834163/10000000000 : ℝ), (-3415733063/10000000000 : ℝ), (4658144957/10000000000 : ℝ)] ![(37143611376919/100000000000000 : ℝ), (25265741150401/100000000000000 : ℝ), (37590647458991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4614834163/10000000000 : ℝ)|^73 ≤ (37143611376919/100000000000000 : ℝ)^57
        have hw : |(4614834163/10000000000 : ℝ)|=(4614834163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3415733063/10000000000 : ℝ)|^73 ≤ (25265741150401/100000000000000 : ℝ)^57
        have hw : |(-3415733063/10000000000 : ℝ)|=(3415733063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4658144957/10000000000 : ℝ)|^73 ≤ (37590647458991/100000000000000 : ℝ)^57
        have hw : |(4658144957/10000000000 : ℝ)|=(4658144957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312086_s2_s2_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-31122863/312500000 : ℝ)*x 0 + (-5743231927/10000000000 : ℝ)*x 1 + (216784973/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (31122863/312500000 : ℝ)^73 ≤ (1303079152119/25000000000000 : ℝ)^57 := by
    have hnat : (31122863 : ℕ)^73*25000000000000^57 ≤ 1303079152119^57*312500000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      31122863 312500000 1303079152119 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5743231927/10000000000 : ℝ)^73 ≤ (12288280873507/25000000000000 : ℝ)^57 := by
    have hnat : (5743231927 : ℕ)^73*25000000000000^57 ≤ 12288280873507^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5743231927 10000000000 12288280873507 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (216784973/400000000 : ℝ)^73 ≤ (4563455988521/10000000000000 : ℝ)^57 := by
    have hnat : (216784973 : ℕ)^73*10000000000000^57 ≤ 4563455988521^57*400000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216784973 400000000 4563455988521 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-31122863/312500000 : ℝ), (-5743231927/10000000000 : ℝ), (216784973/400000000 : ℝ)] ![(1303079152119/25000000000000 : ℝ), (12288280873507/25000000000000 : ℝ), (4563455988521/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-31122863/312500000 : ℝ)|^73 ≤ (1303079152119/25000000000000 : ℝ)^57
        have hw : |(-31122863/312500000 : ℝ)|=(31122863/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5743231927/10000000000 : ℝ)|^73 ≤ (12288280873507/25000000000000 : ℝ)^57
        have hw : |(-5743231927/10000000000 : ℝ)|=(5743231927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(216784973/400000000 : ℝ)|^73 ≤ (4563455988521/10000000000000 : ℝ)^57
        have hw : |(216784973/400000000 : ℝ)|=(216784973/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312086_s2_s2_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2899496709/5000000000 : ℝ)*x 0 + (3485023573/10000000000 : ℝ)*x 1 + (3314509809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2899496709/5000000000 : ℝ)^73 ≤ (24882572849303/50000000000000 : ℝ)^57 := by
    have hnat : (2899496709 : ℕ)^73*50000000000000^57 ≤ 24882572849303^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2899496709 5000000000 24882572849303 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3485023573/10000000000 : ℝ)^73 ≤ (25924002968981/100000000000000 : ℝ)^57 := by
    have hnat : (3485023573 : ℕ)^73*100000000000000^57 ≤ 25924002968981^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3485023573 10000000000 25924002968981 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3314509809/10000000000 : ℝ)^73 ≤ (24310851313789/100000000000000 : ℝ)^57 := by
    have hnat : (3314509809 : ℕ)^73*100000000000000^57 ≤ 24310851313789^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3314509809 10000000000 24310851313789 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2899496709/5000000000 : ℝ), (3485023573/10000000000 : ℝ), (3314509809/10000000000 : ℝ)] ![(24882572849303/50000000000000 : ℝ), (25924002968981/100000000000000 : ℝ), (24310851313789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2899496709/5000000000 : ℝ)|^73 ≤ (24882572849303/50000000000000 : ℝ)^57
        have hw : |(2899496709/5000000000 : ℝ)|=(2899496709/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3485023573/10000000000 : ℝ)|^73 ≤ (25924002968981/100000000000000 : ℝ)^57
        have hw : |(3485023573/10000000000 : ℝ)|=(3485023573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3314509809/10000000000 : ℝ)|^73 ≤ (24310851313789/100000000000000 : ℝ)^57
        have hw : |(3314509809/10000000000 : ℝ)|=(3314509809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312086_s2_s2_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (693124503/1250000000 : ℝ)*x 0 + (-455331991/1250000000 : ℝ)*x 1 + (-3448222669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (693124503/1250000000 : ℝ)^73 ≤ (4699091131779/10000000000000 : ℝ)^57 := by
    have hnat : (693124503 : ℕ)^73*10000000000000^57 ≤ 4699091131779^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693124503 1250000000 4699091131779 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (455331991/1250000000 : ℝ)^73 ≤ (27435157449103/100000000000000 : ℝ)^57 := by
    have hnat : (455331991 : ℕ)^73*100000000000000^57 ≤ 27435157449103^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455331991 1250000000 27435157449103 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3448222669/10000000000 : ℝ)^73 ≤ (1022957248829/4000000000000 : ℝ)^57 := by
    have hnat : (3448222669 : ℕ)^73*4000000000000^57 ≤ 1022957248829^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3448222669 10000000000 1022957248829 4000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(693124503/1250000000 : ℝ), (-455331991/1250000000 : ℝ), (-3448222669/10000000000 : ℝ)] ![(4699091131779/10000000000000 : ℝ), (27435157449103/100000000000000 : ℝ), (1022957248829/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(693124503/1250000000 : ℝ)|^73 ≤ (4699091131779/10000000000000 : ℝ)^57
        have hw : |(693124503/1250000000 : ℝ)|=(693124503/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-455331991/1250000000 : ℝ)|^73 ≤ (27435157449103/100000000000000 : ℝ)^57
        have hw : |(-455331991/1250000000 : ℝ)|=(455331991/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3448222669/10000000000 : ℝ)|^73 ≤ (1022957248829/4000000000000 : ℝ)^57
        have hw : |(-3448222669/10000000000 : ℝ)|=(3448222669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312086_s2_s2_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2245355707/5000000000 : ℝ)*x 0 + (-1643531047/5000000000 : ℝ)*x 1 + (1224270933/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2245355707/5000000000 : ℝ)^73 ≤ (1793450535503/5000000000000 : ℝ)^57 := by
    have hnat : (2245355707 : ℕ)^73*5000000000000^57 ≤ 1793450535503^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245355707 5000000000 1793450535503 5000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1643531047/5000000000 : ℝ)^73 ≤ (4810664124161/20000000000000 : ℝ)^57 := by
    have hnat : (1643531047 : ℕ)^73*20000000000000^57 ≤ 4810664124161^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1643531047 5000000000 4810664124161 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1224270933/2500000000 : ℝ)^73 ≤ (4007766865957/10000000000000 : ℝ)^57 := by
    have hnat : (1224270933 : ℕ)^73*10000000000000^57 ≤ 4007766865957^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1224270933 2500000000 4007766865957 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2245355707/5000000000 : ℝ), (-1643531047/5000000000 : ℝ), (1224270933/2500000000 : ℝ)] ![(1793450535503/5000000000000 : ℝ), (4810664124161/20000000000000 : ℝ), (4007766865957/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2245355707/5000000000 : ℝ)|^73 ≤ (1793450535503/5000000000000 : ℝ)^57
        have hw : |(2245355707/5000000000 : ℝ)|=(2245355707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1643531047/5000000000 : ℝ)|^73 ≤ (4810664124161/20000000000000 : ℝ)^57
        have hw : |(-1643531047/5000000000 : ℝ)|=(1643531047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1224270933/2500000000 : ℝ)|^73 ≤ (4007766865957/10000000000000 : ℝ)^57
        have hw : |(1224270933/2500000000 : ℝ)|=(1224270933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312086_s2_s2_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-231409143/2500000000 : ℝ)*x 0 + (-5621062249/10000000000 : ℝ)*x 1 + (5585966703/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (231409143/2500000000 : ℝ)^73 ≤ (593237443781/12500000000000 : ℝ)^57 := by
    have hnat : (231409143 : ℕ)^73*12500000000000^57 ≤ 593237443781^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231409143 2500000000 593237443781 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5621062249/10000000000 : ℝ)^73 ≤ (5977257867347/12500000000000 : ℝ)^57 := by
    have hnat : (5621062249 : ℕ)^73*12500000000000^57 ≤ 5977257867347^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5621062249 10000000000 5977257867347 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5585966703/10000000000 : ℝ)^73 ≤ (11859009374599/25000000000000 : ℝ)^57 := by
    have hnat : (5585966703 : ℕ)^73*25000000000000^57 ≤ 11859009374599^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5585966703 10000000000 11859009374599 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-231409143/2500000000 : ℝ), (-5621062249/10000000000 : ℝ), (5585966703/10000000000 : ℝ)] ![(593237443781/12500000000000 : ℝ), (5977257867347/12500000000000 : ℝ), (11859009374599/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-231409143/2500000000 : ℝ)|^73 ≤ (593237443781/12500000000000 : ℝ)^57
        have hw : |(-231409143/2500000000 : ℝ)|=(231409143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5621062249/10000000000 : ℝ)|^73 ≤ (5977257867347/12500000000000 : ℝ)^57
        have hw : |(-5621062249/10000000000 : ℝ)|=(5621062249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5585966703/10000000000 : ℝ)|^73 ≤ (11859009374599/25000000000000 : ℝ)^57
        have hw : |(5585966703/10000000000 : ℝ)|=(5585966703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312086_s2_s2_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (587740227/1000000000 : ℝ)*x 0 + (1741897191/5000000000 : ℝ)*x 1 + (1611745041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (587740227/1000000000 : ℝ)^73 ≤ (50628534660683/100000000000000 : ℝ)^57 := by
    have hnat : (587740227 : ℕ)^73*100000000000000^57 ≤ 50628534660683^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      587740227 1000000000 50628534660683 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1741897191/5000000000 : ℝ)^73 ≤ (3239036670591/12500000000000 : ℝ)^57 := by
    have hnat : (1741897191 : ℕ)^73*12500000000000^57 ≤ 3239036670591^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1741897191 5000000000 3239036670591 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1611745041/5000000000 : ℝ)^73 ≤ (23459171969111/100000000000000 : ℝ)^57 := by
    have hnat : (1611745041 : ℕ)^73*100000000000000^57 ≤ 23459171969111^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1611745041 5000000000 23459171969111 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(587740227/1000000000 : ℝ), (1741897191/5000000000 : ℝ), (1611745041/5000000000 : ℝ)] ![(50628534660683/100000000000000 : ℝ), (3239036670591/12500000000000 : ℝ), (23459171969111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(587740227/1000000000 : ℝ)|^73 ≤ (50628534660683/100000000000000 : ℝ)^57
        have hw : |(587740227/1000000000 : ℝ)|=(587740227/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1741897191/5000000000 : ℝ)|^73 ≤ (3239036670591/12500000000000 : ℝ)^57
        have hw : |(1741897191/5000000000 : ℝ)|=(1741897191/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1611745041/5000000000 : ℝ)|^73 ≤ (23459171969111/100000000000000 : ℝ)^57
        have hw : |(1611745041/5000000000 : ℝ)|=(1611745041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312086_s2_s2_16 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2774024619/5000000000 : ℝ)*x 0 + (-369147971/1000000000 : ℝ)*x 1 + (-67898867/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2774024619/5000000000 : ℝ)^73 ≤ (9404810247241/20000000000000 : ℝ)^57 := by
    have hnat : (2774024619 : ℕ)^73*20000000000000^57 ≤ 9404810247241^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2774024619 5000000000 9404810247241 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (369147971/1000000000 : ℝ)^73 ≤ (13953491978879/50000000000000 : ℝ)^57 := by
    have hnat : (369147971 : ℕ)^73*50000000000000^57 ≤ 13953491978879^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      369147971 1000000000 13953491978879 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67898867/200000000 : ℝ)^73 ≤ (25068964789821/100000000000000 : ℝ)^57 := by
    have hnat : (67898867 : ℕ)^73*100000000000000^57 ≤ 25068964789821^57*200000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67898867 200000000 25068964789821 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2774024619/5000000000 : ℝ), (-369147971/1000000000 : ℝ), (-67898867/200000000 : ℝ)] ![(9404810247241/20000000000000 : ℝ), (13953491978879/50000000000000 : ℝ), (25068964789821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2774024619/5000000000 : ℝ)|^73 ≤ (9404810247241/20000000000000 : ℝ)^57
        have hw : |(2774024619/5000000000 : ℝ)|=(2774024619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-369147971/1000000000 : ℝ)|^73 ≤ (13953491978879/50000000000000 : ℝ)^57
        have hw : |(-369147971/1000000000 : ℝ)|=(369147971/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-67898867/200000000 : ℝ)|^73 ≤ (25068964789821/100000000000000 : ℝ)^57
        have hw : |(-67898867/200000000 : ℝ)|=(67898867/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312086_s2_s2_20 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4502543669/10000000000 : ℝ)*x 0 + (-3331617683/10000000000 : ℝ)*x 1 + (4845540953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4502543669/10000000000 : ℝ)^73 ≤ (35990092894719/100000000000000 : ℝ)^57 := by
    have hnat : (4502543669 : ℕ)^73*100000000000000^57 ≤ 35990092894719^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502543669 10000000000 35990092894719 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3331617683/10000000000 : ℝ)^73 ≤ (24471670928219/100000000000000 : ℝ)^57 := by
    have hnat : (3331617683 : ℕ)^73*100000000000000^57 ≤ 24471670928219^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3331617683 10000000000 24471670928219 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4845540953/10000000000 : ℝ)^73 ≤ (39538236165709/100000000000000 : ℝ)^57 := by
    have hnat : (4845540953 : ℕ)^73*100000000000000^57 ≤ 39538236165709^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4845540953 10000000000 39538236165709 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4502543669/10000000000 : ℝ), (-3331617683/10000000000 : ℝ), (4845540953/10000000000 : ℝ)] ![(35990092894719/100000000000000 : ℝ), (24471670928219/100000000000000 : ℝ), (39538236165709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4502543669/10000000000 : ℝ)|^73 ≤ (35990092894719/100000000000000 : ℝ)^57
        have hw : |(4502543669/10000000000 : ℝ)|=(4502543669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3331617683/10000000000 : ℝ)|^73 ≤ (24471670928219/100000000000000 : ℝ)^57
        have hw : |(-3331617683/10000000000 : ℝ)|=(3331617683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4845540953/10000000000 : ℝ)|^73 ≤ (39538236165709/100000000000000 : ℝ)^57
        have hw : |(4845540953/10000000000 : ℝ)|=(4845540953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312086_s2_s2_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-892038183/10000000000 : ℝ)*x 0 + (-1434015763/2500000000 : ℝ)*x 1 + (5490385137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (892038183/10000000000 : ℝ)^73 ≤ (4526413608701/100000000000000 : ℝ)^57 := by
    have hnat : (892038183 : ℕ)^73*100000000000000^57 ≤ 4526413608701^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      892038183 10000000000 4526413608701 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1434015763/2500000000 : ℝ)^73 ≤ (12268640141329/25000000000000 : ℝ)^57 := by
    have hnat : (1434015763 : ℕ)^73*25000000000000^57 ≤ 12268640141329^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1434015763 2500000000 12268640141329 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5490385137/10000000000 : ℝ)^73 ≤ (23199512902583/50000000000000 : ℝ)^57 := by
    have hnat : (5490385137 : ℕ)^73*50000000000000^57 ≤ 23199512902583^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490385137 10000000000 23199512902583 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-892038183/10000000000 : ℝ), (-1434015763/2500000000 : ℝ), (5490385137/10000000000 : ℝ)] ![(4526413608701/100000000000000 : ℝ), (12268640141329/25000000000000 : ℝ), (23199512902583/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-892038183/10000000000 : ℝ)|^73 ≤ (4526413608701/100000000000000 : ℝ)^57
        have hw : |(-892038183/10000000000 : ℝ)|=(892038183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1434015763/2500000000 : ℝ)|^73 ≤ (12268640141329/25000000000000 : ℝ)^57
        have hw : |(-1434015763/2500000000 : ℝ)|=(1434015763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5490385137/10000000000 : ℝ)|^73 ≤ (23199512902583/50000000000000 : ℝ)^57
        have hw : |(5490385137/10000000000 : ℝ)|=(5490385137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312086_s2_s2_22 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5911001851/10000000000 : ℝ)*x 0 + (853757923/2500000000 : ℝ)*x 1 + (130149231/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5911001851/10000000000 : ℝ)^73 ≤ (12749876348311/25000000000000 : ℝ)^57 := by
    have hnat : (5911001851 : ℕ)^73*25000000000000^57 ≤ 12749876348311^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5911001851 10000000000 12749876348311 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (853757923/2500000000 : ℝ)^73 ≤ (6314774280763/25000000000000 : ℝ)^57 := by
    have hnat : (853757923 : ℕ)^73*25000000000000^57 ≤ 6314774280763^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      853757923 2500000000 6314774280763 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130149231/400000000 : ℝ)^73 ≤ (11870698736159/50000000000000 : ℝ)^57 := by
    have hnat : (130149231 : ℕ)^73*50000000000000^57 ≤ 11870698736159^57*400000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130149231 400000000 11870698736159 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5911001851/10000000000 : ℝ), (853757923/2500000000 : ℝ), (130149231/400000000 : ℝ)] ![(12749876348311/25000000000000 : ℝ), (6314774280763/25000000000000 : ℝ), (11870698736159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5911001851/10000000000 : ℝ)|^73 ≤ (12749876348311/25000000000000 : ℝ)^57
        have hw : |(5911001851/10000000000 : ℝ)|=(5911001851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(853757923/2500000000 : ℝ)|^73 ≤ (6314774280763/25000000000000 : ℝ)^57
        have hw : |(853757923/2500000000 : ℝ)|=(853757923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130149231/400000000 : ℝ)|^73 ≤ (11870698736159/50000000000000 : ℝ)^57
        have hw : |(130149231/400000000 : ℝ)|=(130149231/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312086_s2_s2_23 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1100384521/2000000000 : ℝ)*x 0 + (-732482027/2000000000 : ℝ)*x 1 + (-347727617/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1100384521/2000000000 : ℝ)^73 ≤ (11630983617791/25000000000000 : ℝ)^57 := by
    have hnat : (1100384521 : ℕ)^73*25000000000000^57 ≤ 11630983617791^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100384521 2000000000 11630983617791 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (732482027/2000000000 : ℝ)^73 ≤ (27625847005761/100000000000000 : ℝ)^57 := by
    have hnat : (732482027 : ℕ)^73*100000000000000^57 ≤ 27625847005761^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      732482027 2000000000 27625847005761 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (347727617/1000000000 : ℝ)^73 ≤ (6462554627483/25000000000000 : ℝ)^57 := by
    have hnat : (347727617 : ℕ)^73*25000000000000^57 ≤ 6462554627483^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      347727617 1000000000 6462554627483 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1100384521/2000000000 : ℝ), (-732482027/2000000000 : ℝ), (-347727617/1000000000 : ℝ)] ![(11630983617791/25000000000000 : ℝ), (27625847005761/100000000000000 : ℝ), (6462554627483/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1100384521/2000000000 : ℝ)|^73 ≤ (11630983617791/25000000000000 : ℝ)^57
        have hw : |(1100384521/2000000000 : ℝ)|=(1100384521/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-732482027/2000000000 : ℝ)|^73 ≤ (27625847005761/100000000000000 : ℝ)^57
        have hw : |(-732482027/2000000000 : ℝ)|=(732482027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-347727617/1000000000 : ℝ)|^73 ≤ (6462554627483/25000000000000 : ℝ)^57
        have hw : |(-347727617/1000000000 : ℝ)|=(347727617/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312086_s2_s2_27 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4610399451/10000000000 : ℝ)*x 0 + (-3421308263/10000000000 : ℝ)*x 1 + (4657456029/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4610399451/10000000000 : ℝ)^73 ≤ (37097904361743/100000000000000 : ℝ)^57 := by
    have hnat : (4610399451 : ℕ)^73*100000000000000^57 ≤ 37097904361743^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4610399451 10000000000 37097904361743 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3421308263/10000000000 : ℝ)^73 ≤ (25318568158379/100000000000000 : ℝ)^57 := by
    have hnat : (3421308263 : ℕ)^73*100000000000000^57 ≤ 25318568158379^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3421308263 10000000000 25318568158379 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4657456029/10000000000 : ℝ)^73 ≤ (37583527464919/100000000000000 : ℝ)^57 := by
    have hnat : (4657456029 : ℕ)^73*100000000000000^57 ≤ 37583527464919^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4657456029 10000000000 37583527464919 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4610399451/10000000000 : ℝ), (-3421308263/10000000000 : ℝ), (4657456029/10000000000 : ℝ)] ![(37097904361743/100000000000000 : ℝ), (25318568158379/100000000000000 : ℝ), (37583527464919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4610399451/10000000000 : ℝ)|^73 ≤ (37097904361743/100000000000000 : ℝ)^57
        have hw : |(4610399451/10000000000 : ℝ)|=(4610399451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3421308263/10000000000 : ℝ)|^73 ≤ (25318568158379/100000000000000 : ℝ)^57
        have hw : |(-3421308263/10000000000 : ℝ)|=(3421308263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4657456029/10000000000 : ℝ)|^73 ≤ (37583527464919/100000000000000 : ℝ)^57
        have hw : |(4657456029/10000000000 : ℝ)|=(4657456029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312086_s2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((42139/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(42139/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-67443/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-67443/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(63821/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(63821/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((243/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(243/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-9619/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-9619/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15449/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15449/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78337/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78337/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base60 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s2_pow0 : (42139/100000 : ℝ) ^ (9/2 : ℝ) ≤ (1023408494886896681/50000000000000000000 : ℝ) := by
    have hpowers : (42139/100000 : ℝ)^9 ≤ (1023408494886896681/50000000000000000000 : ℝ)^2 := by
      have hnat : (42139 : ℕ)^9*50000000000000000000^2 ≤ 1023408494886896681^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        42139 100000 1023408494886896681 50000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (42139/100000 : ℝ)) (X := (1023408494886896681/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner0a : (51023408494886896681/50000000000000000000 : ℝ) ≤ (627820443742347/625000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (51023408494886896681/50000000000000000000 : ℝ)^2 ≤ (627820443742347/625000000000000 : ℝ)^9 := by
      have hnat : (51023408494886896681 : ℕ)^2*625000000000000^9 ≤ 627820443742347^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51023408494886896681 50000000000000000000 627820443742347 625000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (627820443742347/625000000000000 : ℝ)) (X := (51023408494886896681/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner0b : (26023408494886896681/25000000000000000000 : ℝ) ≤ (504477779916563/500000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (26023408494886896681/25000000000000000000 : ℝ)^2 ≤ (504477779916563/500000000000000 : ℝ)^9 := by
      have hnat : (26023408494886896681 : ℕ)^2*500000000000000^9 ≤ 504477779916563^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26023408494886896681 25000000000000000000 504477779916563 500000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (504477779916563/500000000000000 : ℝ)) (X := (26023408494886896681/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(2820443742347/263368750000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(11107124613427/1053475000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (42139/100000 : ℝ)) (alpha := (2820443742347/263368750000000 : ℝ)) (beta := (11107124613427/1053475000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (42139/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(2820443742347/263368750000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(11107124613427/1053475000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (67443/100000 : ℝ) ^ (9/2 : ℝ) ≤ (16990883476851786941/100000000000000000000 : ℝ) := by
    have hpowers : (67443/100000 : ℝ)^9 ≤ (16990883476851786941/100000000000000000000 : ℝ)^2 := by
      have hnat : (67443 : ℕ)^9*100000000000000000000^2 ≤ 16990883476851786941^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67443 100000 16990883476851786941 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (67443/100000 : ℝ)) (X := (16990883476851786941/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner1a : (116990883476851786941/100000000000000000000 : ℝ) ≤ (10354875783158661/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (116990883476851786941/100000000000000000000 : ℝ)^2 ≤ (10354875783158661/10000000000000000 : ℝ)^9 := by
      have hnat : (116990883476851786941 : ℕ)^2*10000000000000000^9 ≤ 10354875783158661^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        116990883476851786941 100000000000000000000 10354875783158661 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10354875783158661/10000000000000000 : ℝ)) (X := (116990883476851786941/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner1b : (66990883476851786941/50000000000000000000 : ℝ) ≤ (2667917444101477/2500000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (66990883476851786941/50000000000000000000 : ℝ)^2 ≤ (2667917444101477/2500000000000000 : ℝ)^9 := by
      have hnat : (66990883476851786941 : ℕ)^2*2500000000000000^9 ≤ 2667917444101477^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66990883476851786941 50000000000000000000 2667917444101477 2500000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2667917444101477/2500000000000000 : ℝ)) (X := (66990883476851786941/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(354875783158661/6744300000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(316793993247247/6744300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (67443/100000 : ℝ)) (alpha := (354875783158661/6744300000000000 : ℝ)) (beta := (316793993247247/6744300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (67443/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(354875783158661/6744300000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(316793993247247/6744300000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (63821/100000 : ℝ) ^ (9/2 : ℝ) ≤ (6626836046471749941/50000000000000000000 : ℝ) := by
    have hpowers : (63821/100000 : ℝ)^9 ≤ (6626836046471749941/50000000000000000000 : ℝ)^2 := by
      have hnat : (63821 : ℕ)^9*50000000000000000000^2 ≤ 6626836046471749941^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63821 100000 6626836046471749941 50000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (63821/100000 : ℝ)) (X := (6626836046471749941/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner2a : (56626836046471749941/50000000000000000000 : ℝ) ≤ (2570109513381523/2500000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (56626836046471749941/50000000000000000000 : ℝ)^2 ≤ (2570109513381523/2500000000000000 : ℝ)^9 := by
      have hnat : (56626836046471749941 : ℕ)^2*2500000000000000^9 ≤ 2570109513381523^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56626836046471749941 50000000000000000000 2570109513381523 2500000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2570109513381523/2500000000000000 : ℝ)) (X := (56626836046471749941/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s2_corner2b : (31626836046471749941/25000000000000000000 : ℝ) ≤ (329262603623083/312500000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (31626836046471749941/25000000000000000000 : ℝ)^2 ≤ (329262603623083/312500000000000 : ℝ)^9 := by
      have hnat : (31626836046471749941 : ℕ)^2*312500000000000^9 ≤ 329262603623083^9*25000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31626836046471749941 25000000000000000000 329262603623083 312500000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (329262603623083/312500000000000 : ℝ)) (X := (31626836046471749941/25000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(70109513381523/1595525000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(63991315603141/1595525000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (63821/100000 : ℝ)) (alpha := (70109513381523/1595525000000000 : ℝ)) (beta := (63991315603141/1595525000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (63821/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(70109513381523/1595525000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(63991315603141/1595525000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-1000679623/10000000000 : ℝ)*X 0 0+(-1127918003/2000000000 : ℝ)*X 0 1+(1380369687/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312086_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((5801951057/10000000000 : ℝ)*X 1 0+(436922353/1250000000 : ℝ)*X 1 1+(1650267161/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312086_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((4614834163/10000000000 : ℝ)*X 0 0+(-3415733063/10000000000 : ℝ)*X 0 1+(4658144957/10000000000 : ℝ)*X 0 2+(4614834163/10000000000 : ℝ)*X 1 0+(-3415733063/10000000000 : ℝ)*X 1 1+(4658144957/10000000000 : ℝ)*X 1 2+(4614834163/10000000000 : ℝ)*X 2 0+(-3415733063/10000000000 : ℝ)*X 2 1+(4658144957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312086_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-31122863/312500000 : ℝ)*X 0 0+(-5743231927/10000000000 : ℝ)*X 0 1+(216784973/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312086_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((2899496709/5000000000 : ℝ)*X 1 0+(3485023573/10000000000 : ℝ)*X 1 1+(3314509809/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312086_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((693124503/1250000000 : ℝ)*X 2 0+(-455331991/1250000000 : ℝ)*X 2 1+(-3448222669/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312086_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((2245355707/5000000000 : ℝ)*X 0 0+(-1643531047/5000000000 : ℝ)*X 0 1+(1224270933/2500000000 : ℝ)*X 0 2+(2245355707/5000000000 : ℝ)*X 1 0+(-1643531047/5000000000 : ℝ)*X 1 1+(1224270933/2500000000 : ℝ)*X 1 2+(2245355707/5000000000 : ℝ)*X 2 0+(-1643531047/5000000000 : ℝ)*X 2 1+(1224270933/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312086_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-231409143/2500000000 : ℝ)*X 0 0+(-5621062249/10000000000 : ℝ)*X 0 1+(5585966703/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312086_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((587740227/1000000000 : ℝ)*X 1 0+(1741897191/5000000000 : ℝ)*X 1 1+(1611745041/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312086_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((2774024619/5000000000 : ℝ)*X 2 0+(-369147971/1000000000 : ℝ)*X 2 1+(-67898867/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312086_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((4502543669/10000000000 : ℝ)*X 0 0+(-3331617683/10000000000 : ℝ)*X 0 1+(4845540953/10000000000 : ℝ)*X 0 2+(4502543669/10000000000 : ℝ)*X 1 0+(-3331617683/10000000000 : ℝ)*X 1 1+(4845540953/10000000000 : ℝ)*X 1 2+(4502543669/10000000000 : ℝ)*X 2 0+(-3331617683/10000000000 : ℝ)*X 2 1+(4845540953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312086_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-892038183/10000000000 : ℝ)*X 0 0+(-1434015763/2500000000 : ℝ)*X 0 1+(5490385137/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312086_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((5911001851/10000000000 : ℝ)*X 1 0+(853757923/2500000000 : ℝ)*X 1 1+(130149231/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312086_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((1100384521/2000000000 : ℝ)*X 2 0+(-732482027/2000000000 : ℝ)*X 2 1+(-347727617/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312086_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((4610399451/10000000000 : ℝ)*X 0 0+(-3421308263/10000000000 : ℝ)*X 0 1+(4657456029/10000000000 : ℝ)*X 0 2+(4610399451/10000000000 : ℝ)*X 1 0+(-3421308263/10000000000 : ℝ)*X 1 1+(4657456029/10000000000 : ℝ)*X 1 2+(4610399451/10000000000 : ℝ)*X 2 0+(-3421308263/10000000000 : ℝ)*X 2 1+(4657456029/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312086_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((243/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(243/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13762735105843470390471/3191050000000000000000000000 : ℝ) := by norm_num
    linear_combination (8647632106809/1000000000000 : ℝ)*(base40) + (264141847157/200000000000 : ℝ)*(base60) + (34203727688059/1000000000000 : ℝ)*(major_s2_0) + (34203727688059/1000000000000 : ℝ)*(major_s2_1) + (34203727688059/1000000000000 : ℝ)*(major_s2_2) + (323231031/1000000000000 : ℝ)*(sp_s2_1) + (47915402298179/1000000000000 : ℝ)*(sp_s2_7) + (47915057895741/1000000000000 : ℝ)*(sp_s2_8) + (23957405033019/500000000000 : ℝ)*(sp_s2_9) + (20491453943709/1000000000000 : ℝ)*(sp_s2_13) + (123891937/250000000000 : ℝ)*(sp_s2_20) + (51064419/500000000000 : ℝ)*(sp_s2_21) + (24660049/200000000000 : ℝ)*(sp_s2_22) + (694360979/1000000000000 : ℝ)*(sp_s2_23) + (10245974755729/500000000000 : ℝ)*(f.failure) + (47915504427017/1000000000000 : ℝ)*(f.sum) + (215259127651605183437/430427970300000000000000000000000 : ℝ)*base63 + (1433474363203457/3191050000000000000000000000 : ℝ)*base65 + (884541785482591/6744300000000000000000000000 : ℝ)*base66 + (13433996910139/199440625000000000000000000 : ℝ)*base69 + (15410975919326470483/134467655950000000000000000000000 : ℝ)*base70 + (4520922522303/263368750000000000000000000 : ℝ)*base72 + (1060989506618777/6744300000000000000000000000 : ℝ)*base74 + (232610366387289/2106950000000000000000000000 : ℝ)*base77 + (120494539143568566257/284198057700000000000000000000000 : ℝ)*base79 + (44577/50000000000000000 : ℝ)*base87 + (44577/50000000000000000 : ℝ)*base89 + (44577/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-9619/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-9619/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6908453781198259035117/2106950000000000000000000000 : ℝ) := by norm_num
    linear_combination (132669/100000000000 : ℝ)*(base39) + (6645326949057/500000000000 : ℝ)*(base40) + (2432362284737/1000000000000 : ℝ)*(base60) + (49469070139471/1000000000000 : ℝ)*(major_s2_0) + (49469070139471/1000000000000 : ℝ)*(major_s2_1) + (49469070139471/1000000000000 : ℝ)*(major_s2_2) + (409425107/1000000000000 : ℝ)*(sp_s2_0) + (87808673/500000000000 : ℝ)*(sp_s2_6) + (455218373/1000000000000 : ℝ)*(sp_s2_13) + (69300092105641/1000000000000 : ℝ)*(sp_s2_14) + (13860091092293/200000000000 : ℝ)*(sp_s2_15) + (17325125382687/250000000000 : ℝ)*(sp_s2_16) + (29637006819509/1000000000000 : ℝ)*(sp_s2_20) + (46069283/1000000000000 : ℝ)*(sp_s2_22) + (7409409413807/250000000000 : ℝ)*(f.failure) + (17325125382687/250000000000 : ℝ)*(f.sum) + (69304148302251238913/430427970300000000000000000000000 : ℝ)*base63 + (503668631587883/3191050000000000000000000000 : ℝ)*base65 + (417640124162089/6744300000000000000000000000 : ℝ)*base66 + (46010345989177/1595525000000000000000000000 : ℝ)*base68 + (33482750810154585647/134467655950000000000000000000000 : ℝ)*base70 + (193812168466171/526737500000000000000000000 : ℝ)*base73 + (520850151250613/6744300000000000000000000000 : ℝ)*base74 + (259697890814539/2106950000000000000000000000 : ℝ)*base76 + (156940309914632697383/284198057700000000000000000000000 : ℝ)*base79 + (7209/25000000000000000 : ℝ)*base86 + (7209/25000000000000000 : ℝ)*base88 + (7209/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15449/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15449/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (21678245016979549195162033210679/3022967373411950000000000000000000000 : ℝ) := by norm_num
    linear_combination (1342939/1000000000000 : ℝ)*(base39) + (1179022675429/125000000000 : ℝ)*(base40) + (99099/40000000000 : ℝ)*(base50) + (549005732451/500000000000 : ℝ)*(base60) + (34772550375473/1000000000000 : ℝ)*(major_s2_0) + (34772550375473/1000000000000 : ℝ)*(major_s2_1) + (34772550375473/1000000000000 : ℝ)*(major_s2_2) + (8693119193/1000000000000 : ℝ)*(sp_s2_0) + (4239581373/500000000000 : ℝ)*(sp_s2_8) + (85340093/500000000000 : ℝ)*(sp_s2_14) + (12175873781193/250000000000 : ℝ)*(sp_s2_21) + (12175969940351/250000000000 : ℝ)*(sp_s2_22) + (48712358924151/1000000000000 : ℝ)*(sp_s2_23) + (20832739436397/1000000000000 : ℝ)*(sp_s2_27) + (20832739436397/1000000000000 : ℝ)*(f.failure) + (48712358924151/1000000000000 : ℝ)*(f.sum) + (204063396869606533361/430427970300000000000000000000000 : ℝ)*base62 + (138839472957417/1595525000000000000000000000 : ℝ)*base65 + (1928172699884083/6744300000000000000000000000 : ℝ)*base67 + (1556142161388463/3191050000000000000000000000 : ℝ)*base69 + (34755334706821088829/134467655950000000000000000000000 : ℝ)*base71 + (942924698448677/2106950000000000000000000000 : ℝ)*base73 + (3335782858478029/6744300000000000000000000000 : ℝ)*base74 + (39626094058933/526737500000000000000000000 : ℝ)*base76 + (149991110795041670269/284198057700000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (32461/100000000000000000 : ℝ)*base87 + (32461/100000000000000000 : ℝ)*base89 + (32461/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((42139/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(42139/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-67443/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-67443/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(63821/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(63821/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((243/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(243/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-9619/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-9619/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15449/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15449/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c312086_s2 p hpa hpb X hX hprev1

#print axioms solution
