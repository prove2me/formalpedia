-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301057_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:34:08.419447+00:00
-- url     : https://prove2.me/submissions/5028ac7e-8f5d-4333-a119-ba5f68e2b663

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
theorem collision_support_c301057_s1_s1_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1554896093/5000000000 : ℝ)*x 0 + (386575379/1250000000 : ℝ)*x 1 + (1651197613/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1554896093/5000000000 : ℝ)^65 ≤ (16989579029/80000000000 : ℝ)^49 := by
    have hnat : (1554896093 : ℕ)^65*80000000000^49 ≤ 16989579029^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1554896093 5000000000 16989579029 80000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (386575379/1250000000 : ℝ)^65 ≤ (32939685243/156250000000 : ℝ)^49 := by
    have hnat : (386575379 : ℕ)^65*156250000000^49 ≤ 32939685243^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386575379 1250000000 32939685243 156250000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1651197613/2500000000 : ℝ)^65 ≤ (7210203454431/12500000000000 : ℝ)^49 := by
    have hnat : (1651197613 : ℕ)^65*12500000000000^49 ≤ 7210203454431^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1651197613 2500000000 7210203454431 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1554896093/5000000000 : ℝ), (386575379/1250000000 : ℝ), (1651197613/2500000000 : ℝ)] ![(16989579029/80000000000 : ℝ), (32939685243/156250000000 : ℝ), (7210203454431/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1554896093/5000000000 : ℝ)|^65 ≤ (16989579029/80000000000 : ℝ)^49
        have hw : |(-1554896093/5000000000 : ℝ)|=(1554896093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(386575379/1250000000 : ℝ)|^65 ≤ (32939685243/156250000000 : ℝ)^49
        have hw : |(386575379/1250000000 : ℝ)|=(386575379/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1651197613/2500000000 : ℝ)|^65 ≤ (7210203454431/12500000000000 : ℝ)^49
        have hw : |(1651197613/2500000000 : ℝ)|=(1651197613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s1_s1_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (775181897/2500000000 : ℝ)*x 0 + (-1541794269/5000000000 : ℝ)*x 1 + (661890313/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (775181897/2500000000 : ℝ)^65 ≤ (21154897022319/100000000000000 : ℝ)^49 := by
    have hnat : (775181897 : ℕ)^65*100000000000000^49 ≤ 21154897022319^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      775181897 2500000000 21154897022319 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1541794269/5000000000 : ℝ)^65 ≤ (839996922411/4000000000000 : ℝ)^49 := by
    have hnat : (1541794269 : ℕ)^65*4000000000000^49 ≤ 839996922411^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1541794269 5000000000 839996922411 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (661890313/1000000000 : ℝ)^65 ≤ (28922589953241/50000000000000 : ℝ)^49 := by
    have hnat : (661890313 : ℕ)^65*50000000000000^49 ≤ 28922589953241^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661890313 1000000000 28922589953241 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(775181897/2500000000 : ℝ), (-1541794269/5000000000 : ℝ), (661890313/1000000000 : ℝ)] ![(21154897022319/100000000000000 : ℝ), (839996922411/4000000000000 : ℝ), (28922589953241/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(775181897/2500000000 : ℝ)|^65 ≤ (21154897022319/100000000000000 : ℝ)^49
        have hw : |(775181897/2500000000 : ℝ)|=(775181897/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1541794269/5000000000 : ℝ)|^65 ≤ (839996922411/4000000000000 : ℝ)^49
        have hw : |(-1541794269/5000000000 : ℝ)|=(1541794269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(661890313/1000000000 : ℝ)|^65 ≤ (28922589953241/50000000000000 : ℝ)^49
        have hw : |(661890313/1000000000 : ℝ)|=(661890313/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s1_s1_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5918394241/10000000000 : ℝ)*x 0 + (1485359541/2500000000 : ℝ)*x 1 + (6874153/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5918394241/10000000000 : ℝ)^65 ≤ (24933973461081/50000000000000 : ℝ)^49 := by
    have hnat : (5918394241 : ℕ)^65*50000000000000^49 ≤ 24933973461081^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5918394241 10000000000 24933973461081 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1485359541/2500000000 : ℝ)^65 ≤ (15664274421/31250000000 : ℝ)^49 := by
    have hnat : (1485359541 : ℕ)^65*31250000000^49 ≤ 15664274421^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1485359541 2500000000 15664274421 31250000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6874153/10000000000 : ℝ)^65 ≤ (6374915627/100000000000000 : ℝ)^49 := by
    have hnat : (6874153 : ℕ)^65*100000000000000^49 ≤ 6374915627^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6874153 10000000000 6374915627 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5918394241/10000000000 : ℝ), (1485359541/2500000000 : ℝ), (6874153/10000000000 : ℝ)] ![(24933973461081/50000000000000 : ℝ), (15664274421/31250000000 : ℝ), (6374915627/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5918394241/10000000000 : ℝ)|^65 ≤ (24933973461081/50000000000000 : ℝ)^49
        have hw : |(5918394241/10000000000 : ℝ)|=(5918394241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1485359541/2500000000 : ℝ)|^65 ≤ (15664274421/31250000000 : ℝ)^49
        have hw : |(1485359541/2500000000 : ℝ)|=(1485359541/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6874153/10000000000 : ℝ)|^65 ≤ (6374915627/100000000000000 : ℝ)^49
        have hw : |(6874153/10000000000 : ℝ)|=(6874153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s1_s1_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1922900361/10000000000 : ℝ)*x 0 + (454385407/5000000000 : ℝ)*x 1 + (4408670781/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1922900361/10000000000 : ℝ)^65 ≤ (1122397653977/10000000000000 : ℝ)^49 := by
    have hnat : (1922900361 : ℕ)^65*10000000000000^49 ≤ 1122397653977^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1922900361 10000000000 1122397653977 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (454385407/5000000000 : ℝ)^65 ≤ (2076480433721/50000000000000 : ℝ)^49 := by
    have hnat : (454385407 : ℕ)^65*50000000000000^49 ≤ 2076480433721^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454385407 5000000000 2076480433721 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4408670781/5000000000 : ℝ)^65 ≤ (84623062581519/100000000000000 : ℝ)^49 := by
    have hnat : (4408670781 : ℕ)^65*100000000000000^49 ≤ 84623062581519^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4408670781 5000000000 84623062581519 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1922900361/10000000000 : ℝ), (454385407/5000000000 : ℝ), (4408670781/5000000000 : ℝ)] ![(1122397653977/10000000000000 : ℝ), (2076480433721/50000000000000 : ℝ), (84623062581519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1922900361/10000000000 : ℝ)|^65 ≤ (1122397653977/10000000000000 : ℝ)^49
        have hw : |(-1922900361/10000000000 : ℝ)|=(1922900361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(454385407/5000000000 : ℝ)|^65 ≤ (2076480433721/50000000000000 : ℝ)^49
        have hw : |(454385407/5000000000 : ℝ)|=(454385407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4408670781/5000000000 : ℝ)|^65 ≤ (84623062581519/100000000000000 : ℝ)^49
        have hw : |(4408670781/5000000000 : ℝ)|=(4408670781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s1_s1_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1186048811/10000000000 : ℝ)*x 0 + (-1658510989/10000000000 : ℝ)*x 1 + (2209050319/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1186048811/10000000000 : ℝ)^65 ≤ (2956233333627/50000000000000 : ℝ)^49 := by
    have hnat : (1186048811 : ℕ)^65*50000000000000^49 ≤ 2956233333627^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1186048811 10000000000 2956233333627 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1658510989/10000000000 : ℝ)^65 ≤ (4612140342911/50000000000000 : ℝ)^49 := by
    have hnat : (1658510989 : ℕ)^65*50000000000000^49 ≤ 4612140342911^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1658510989 10000000000 4612140342911 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2209050319/2500000000 : ℝ)^65 ≤ (21215813158317/25000000000000 : ℝ)^49 := by
    have hnat : (2209050319 : ℕ)^65*25000000000000^49 ≤ 21215813158317^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2209050319 2500000000 21215813158317 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1186048811/10000000000 : ℝ), (-1658510989/10000000000 : ℝ), (2209050319/2500000000 : ℝ)] ![(2956233333627/50000000000000 : ℝ), (4612140342911/50000000000000 : ℝ), (21215813158317/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1186048811/10000000000 : ℝ)|^65 ≤ (2956233333627/50000000000000 : ℝ)^49
        have hw : |(1186048811/10000000000 : ℝ)|=(1186048811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1658510989/10000000000 : ℝ)|^65 ≤ (4612140342911/50000000000000 : ℝ)^49
        have hw : |(-1658510989/10000000000 : ℝ)|=(1658510989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2209050319/2500000000 : ℝ)|^65 ≤ (21215813158317/25000000000000 : ℝ)^49
        have hw : |(2209050319/2500000000 : ℝ)|=(2209050319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s1_s1_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3185304157/10000000000 : ℝ)*x 0 + (829804717/1000000000 : ℝ)*x 1 + (27/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3185304157/10000000000 : ℝ)^65 ≤ (21923731281733/100000000000000 : ℝ)^49 := by
    have hnat : (3185304157 : ℕ)^65*100000000000000^49 ≤ 21923731281733^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3185304157 10000000000 21923731281733 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (829804717/1000000000 : ℝ)^65 ≤ (78076268696089/100000000000000 : ℝ)^49 := by
    have hnat : (829804717 : ℕ)^65*100000000000000^49 ≤ 78076268696089^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829804717 1000000000 78076268696089 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27/2000000000 : ℝ)^65 ≤ (3637/100000000000000 : ℝ)^49 := by
    have hnat : (27 : ℕ)^65*100000000000000^49 ≤ 3637^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27 2000000000 3637 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3185304157/10000000000 : ℝ), (829804717/1000000000 : ℝ), (27/2000000000 : ℝ)] ![(21923731281733/100000000000000 : ℝ), (78076268696089/100000000000000 : ℝ), (3637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3185304157/10000000000 : ℝ)|^65 ≤ (21923731281733/100000000000000 : ℝ)^49
        have hw : |(3185304157/10000000000 : ℝ)|=(3185304157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(829804717/1000000000 : ℝ)|^65 ≤ (78076268696089/100000000000000 : ℝ)^49
        have hw : |(829804717/1000000000 : ℝ)|=(829804717/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(27/2000000000 : ℝ)|^65 ≤ (3637/100000000000000 : ℝ)^49
        have hw : |(27/2000000000 : ℝ)|=(27/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s1_s1_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1393474913/5000000000 : ℝ)*x 0 + (3778743387/5000000000 : ℝ)*x 1 + (210637421/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1393474913/5000000000 : ℝ)^65 ≤ (3672627040019/20000000000000 : ℝ)^49 := by
    have hnat : (1393474913 : ℕ)^65*20000000000000^49 ≤ 3672627040019^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1393474913 5000000000 3672627040019 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3778743387/5000000000 : ℝ)^65 ≤ (13794116452651/20000000000000 : ℝ)^49 := by
    have hnat : (3778743387 : ℕ)^65*20000000000000^49 ≤ 13794116452651^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3778743387 5000000000 13794116452651 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210637421/1000000000 : ℝ)^65 ≤ (3166570630463/25000000000000 : ℝ)^49 := by
    have hnat : (210637421 : ℕ)^65*25000000000000^49 ≤ 3166570630463^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210637421 1000000000 3166570630463 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1393474913/5000000000 : ℝ), (3778743387/5000000000 : ℝ), (210637421/1000000000 : ℝ)] ![(3672627040019/20000000000000 : ℝ), (13794116452651/20000000000000 : ℝ), (3166570630463/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1393474913/5000000000 : ℝ)|^65 ≤ (3672627040019/20000000000000 : ℝ)^49
        have hw : |(1393474913/5000000000 : ℝ)|=(1393474913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3778743387/5000000000 : ℝ)|^65 ≤ (13794116452651/20000000000000 : ℝ)^49
        have hw : |(3778743387/5000000000 : ℝ)|=(3778743387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210637421/1000000000 : ℝ)|^65 ≤ (3166570630463/25000000000000 : ℝ)^49
        have hw : |(210637421/1000000000 : ℝ)|=(210637421/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s1_s1_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1683314961/10000000000 : ℝ)*x 0 + (296949577/2500000000 : ℝ)*x 1 + (8820889489/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1683314961/10000000000 : ℝ)^65 ≤ (4703863348077/50000000000000 : ℝ)^49 := by
    have hnat : (1683314961 : ℕ)^65*50000000000000^49 ≤ 4703863348077^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1683314961 10000000000 4703863348077 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (296949577/2500000000 : ℝ)^65 ≤ (1184807694757/20000000000000 : ℝ)^49 := by
    have hnat : (296949577 : ℕ)^65*20000000000000^49 ≤ 1184807694757^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      296949577 2500000000 1184807694757 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8820889489/10000000000 : ℝ)^65 ≤ (42334117406949/50000000000000 : ℝ)^49 := by
    have hnat : (8820889489 : ℕ)^65*50000000000000^49 ≤ 42334117406949^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8820889489 10000000000 42334117406949 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1683314961/10000000000 : ℝ), (296949577/2500000000 : ℝ), (8820889489/10000000000 : ℝ)] ![(4703863348077/50000000000000 : ℝ), (1184807694757/20000000000000 : ℝ), (42334117406949/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1683314961/10000000000 : ℝ)|^65 ≤ (4703863348077/50000000000000 : ℝ)^49
        have hw : |(-1683314961/10000000000 : ℝ)|=(1683314961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(296949577/2500000000 : ℝ)|^65 ≤ (1184807694757/20000000000000 : ℝ)^49
        have hw : |(296949577/2500000000 : ℝ)|=(296949577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8820889489/10000000000 : ℝ)|^65 ≤ (42334117406949/50000000000000 : ℝ)^49
        have hw : |(8820889489/10000000000 : ℝ)|=(8820889489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s1_s1_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (229455241/2500000000 : ℝ)*x 0 + (-37575343/200000000 : ℝ)*x 1 + (8839756211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (229455241/2500000000 : ℝ)^65 ≤ (262994530471/6250000000000 : ℝ)^49 := by
    have hnat : (229455241 : ℕ)^65*6250000000000^49 ≤ 262994530471^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      229455241 2500000000 262994530471 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37575343/200000000 : ℝ)^65 ≤ (2720885455149/25000000000000 : ℝ)^49 := by
    have hnat : (37575343 : ℕ)^65*25000000000000^49 ≤ 2720885455149^49*200000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37575343 200000000 2720885455149 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8839756211/10000000000 : ℝ)^65 ≤ (3396341827207/4000000000000 : ℝ)^49 := by
    have hnat : (8839756211 : ℕ)^65*4000000000000^49 ≤ 3396341827207^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8839756211 10000000000 3396341827207 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(229455241/2500000000 : ℝ), (-37575343/200000000 : ℝ), (8839756211/10000000000 : ℝ)] ![(262994530471/6250000000000 : ℝ), (2720885455149/25000000000000 : ℝ), (3396341827207/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(229455241/2500000000 : ℝ)|^65 ≤ (262994530471/6250000000000 : ℝ)^49
        have hw : |(229455241/2500000000 : ℝ)|=(229455241/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-37575343/200000000 : ℝ)|^65 ≤ (2720885455149/25000000000000 : ℝ)^49
        have hw : |(-37575343/200000000 : ℝ)|=(37575343/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8839756211/10000000000 : ℝ)|^65 ≤ (3396341827207/4000000000000 : ℝ)^49
        have hw : |(8839756211/10000000000 : ℝ)|=(8839756211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s1_s1_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (8291603153/10000000000 : ℝ)*x 0 + (1597054133/5000000000 : ℝ)*x 1 + (33/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8291603153/10000000000 : ℝ)^65 ≤ (2437370283557/3125000000000 : ℝ)^49 := by
    have hnat : (8291603153 : ℕ)^65*3125000000000^49 ≤ 2437370283557^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8291603153 10000000000 2437370283557 3125000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1597054133/5000000000 : ℝ)^65 ≤ (550103772763/2500000000000 : ℝ)^49 := by
    have hnat : (1597054133 : ℕ)^65*2500000000000^49 ≤ 550103772763^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1597054133 5000000000 550103772763 2500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (33/2000000000 : ℝ)^65 ≤ (2373/50000000000000 : ℝ)^49 := by
    have hnat : (33 : ℕ)^65*50000000000000^49 ≤ 2373^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33 2000000000 2373 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8291603153/10000000000 : ℝ), (1597054133/5000000000 : ℝ), (33/2000000000 : ℝ)] ![(2437370283557/3125000000000 : ℝ), (550103772763/2500000000000 : ℝ), (2373/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8291603153/10000000000 : ℝ)|^65 ≤ (2437370283557/3125000000000 : ℝ)^49
        have hw : |(8291603153/10000000000 : ℝ)|=(8291603153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1597054133/5000000000 : ℝ)|^65 ≤ (550103772763/2500000000000 : ℝ)^49
        have hw : |(1597054133/5000000000 : ℝ)|=(1597054133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(33/2000000000 : ℝ)|^65 ≤ (2373/50000000000000 : ℝ)^49
        have hw : |(33/2000000000 : ℝ)|=(33/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s1_s1_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7532141871/10000000000 : ℝ)*x 0 + (2819409379/10000000000 : ℝ)*x 1 + (52729573/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7532141871/10000000000 : ℝ)^65 ≤ (34331961399253/50000000000000 : ℝ)^49 := by
    have hnat : (7532141871 : ℕ)^65*50000000000000^49 ≤ 34331961399253^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7532141871 10000000000 34331961399253 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2819409379/10000000000 : ℝ)^65 ≤ (3729477029899/20000000000000 : ℝ)^49 := by
    have hnat : (2819409379 : ℕ)^65*20000000000000^49 ≤ 3729477029899^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2819409379 10000000000 3729477029899 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52729573/250000000 : ℝ)^65 ≤ (507547681207/4000000000000 : ℝ)^49 := by
    have hnat : (52729573 : ℕ)^65*4000000000000^49 ≤ 507547681207^49*250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52729573 250000000 507547681207 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7532141871/10000000000 : ℝ), (2819409379/10000000000 : ℝ), (52729573/250000000 : ℝ)] ![(34331961399253/50000000000000 : ℝ), (3729477029899/20000000000000 : ℝ), (507547681207/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7532141871/10000000000 : ℝ)|^65 ≤ (34331961399253/50000000000000 : ℝ)^49
        have hw : |(7532141871/10000000000 : ℝ)|=(7532141871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2819409379/10000000000 : ℝ)|^65 ≤ (3729477029899/20000000000000 : ℝ)^49
        have hw : |(2819409379/10000000000 : ℝ)|=(2819409379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52729573/250000000 : ℝ)|^65 ≤ (507547681207/4000000000000 : ℝ)^49
        have hw : |(52729573/250000000 : ℝ)|=(52729573/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s1_s1_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2921971447/5000000000 : ℝ)*x 0 + (2299620553/10000000000 : ℝ)*x 1 + (2350072949/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2921971447/5000000000 : ℝ)^65 ≤ (12259374935111/25000000000000 : ℝ)^49 := by
    have hnat : (2921971447 : ℕ)^65*25000000000000^49 ≤ 12259374935111^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2921971447 5000000000 12259374935111 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2299620553/10000000000 : ℝ)^65 ≤ (142304090399/1000000000000 : ℝ)^49 := by
    have hnat : (2299620553 : ℕ)^65*1000000000000^49 ≤ 142304090399^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2299620553 10000000000 142304090399 1000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2350072949/5000000000 : ℝ)^65 ≤ (7346418240761/20000000000000 : ℝ)^49 := by
    have hnat : (2350072949 : ℕ)^65*20000000000000^49 ≤ 7346418240761^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2350072949 5000000000 7346418240761 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2921971447/5000000000 : ℝ), (2299620553/10000000000 : ℝ), (2350072949/5000000000 : ℝ)] ![(12259374935111/25000000000000 : ℝ), (142304090399/1000000000000 : ℝ), (7346418240761/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2921971447/5000000000 : ℝ)|^65 ≤ (12259374935111/25000000000000 : ℝ)^49
        have hw : |(-2921971447/5000000000 : ℝ)|=(2921971447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2299620553/10000000000 : ℝ)|^65 ≤ (142304090399/1000000000000 : ℝ)^49
        have hw : |(2299620553/10000000000 : ℝ)|=(2299620553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2350072949/5000000000 : ℝ)|^65 ≤ (7346418240761/20000000000000 : ℝ)^49
        have hw : |(2350072949/5000000000 : ℝ)|=(2350072949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s1_s1_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (146652919/10000000000 : ℝ)*x 0 + (-5371107997/10000000000 : ℝ)*x 1 + (3220221017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (146652919/10000000000 : ℝ)^65 ≤ (369426882511/100000000000000 : ℝ)^49 := by
    have hnat : (146652919 : ℕ)^65*100000000000000^49 ≤ 369426882511^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146652919 10000000000 369426882511 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5371107997/10000000000 : ℝ)^65 ≤ (43845141891791/100000000000000 : ℝ)^49 := by
    have hnat : (5371107997 : ℕ)^65*100000000000000^49 ≤ 43845141891791^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5371107997 10000000000 43845141891791 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3220221017/5000000000 : ℝ)^65 ≤ (55785431208709/100000000000000 : ℝ)^49 := by
    have hnat : (3220221017 : ℕ)^65*100000000000000^49 ≤ 55785431208709^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3220221017 5000000000 55785431208709 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(146652919/10000000000 : ℝ), (-5371107997/10000000000 : ℝ), (3220221017/5000000000 : ℝ)] ![(369426882511/100000000000000 : ℝ), (43845141891791/100000000000000 : ℝ), (55785431208709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(146652919/10000000000 : ℝ)|^65 ≤ (369426882511/100000000000000 : ℝ)^49
        have hw : |(146652919/10000000000 : ℝ)|=(146652919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5371107997/10000000000 : ℝ)|^65 ≤ (43845141891791/100000000000000 : ℝ)^49
        have hw : |(-5371107997/10000000000 : ℝ)|=(5371107997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3220221017/5000000000 : ℝ)|^65 ≤ (55785431208709/100000000000000 : ℝ)^49
        have hw : |(3220221017/5000000000 : ℝ)|=(3220221017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s1_s1_23 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1583400387/2500000000 : ℝ)*x 0 + (341272663/625000000 : ℝ)*x 1 + (217875681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1583400387/2500000000 : ℝ)^65 ≤ (54561164655933/100000000000000 : ℝ)^49 := by
    have hnat : (1583400387 : ℕ)^65*100000000000000^49 ≤ 54561164655933^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1583400387 2500000000 54561164655933 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341272663/625000000 : ℝ)^65 ≤ (22407131278891/50000000000000 : ℝ)^49 := by
    have hnat : (341272663 : ℕ)^65*50000000000000^49 ≤ 22407131278891^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341272663 625000000 22407131278891 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217875681/10000000000 : ℝ)^65 ≤ (624572769611/100000000000000 : ℝ)^49 := by
    have hnat : (217875681 : ℕ)^65*100000000000000^49 ≤ 624572769611^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217875681 10000000000 624572769611 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1583400387/2500000000 : ℝ), (341272663/625000000 : ℝ), (217875681/10000000000 : ℝ)] ![(54561164655933/100000000000000 : ℝ), (22407131278891/50000000000000 : ℝ), (624572769611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1583400387/2500000000 : ℝ)|^65 ≤ (54561164655933/100000000000000 : ℝ)^49
        have hw : |(1583400387/2500000000 : ℝ)|=(1583400387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(341272663/625000000 : ℝ)|^65 ≤ (22407131278891/50000000000000 : ℝ)^49
        have hw : |(341272663/625000000 : ℝ)|=(341272663/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217875681/10000000000 : ℝ)|^65 ≤ (624572769611/100000000000000 : ℝ)^49
        have hw : |(217875681/10000000000 : ℝ)|=(217875681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301057_s1_s1_27 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (305989013/1250000000 : ℝ)*x 0 + (341272663/625000000 : ℝ)*x 1 + (4986079181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (305989013/1250000000 : ℝ)^65 ≤ (154603365819/1000000000000 : ℝ)^49 := by
    have hnat : (305989013 : ℕ)^65*1000000000000^49 ≤ 154603365819^49*1250000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      305989013 1250000000 154603365819 1000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (341272663/625000000 : ℝ)^65 ≤ (22407131278891/50000000000000 : ℝ)^49 := by
    have hnat : (341272663 : ℕ)^65*50000000000000^49 ≤ 22407131278891^49*625000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341272663 625000000 22407131278891 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4986079181/10000000000 : ℝ)^65 ≤ (39725400840861/100000000000000 : ℝ)^49 := by
    have hnat : (4986079181 : ℕ)^65*100000000000000^49 ≤ 39725400840861^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4986079181 10000000000 39725400840861 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(305989013/1250000000 : ℝ), (341272663/625000000 : ℝ), (4986079181/10000000000 : ℝ)] ![(154603365819/1000000000000 : ℝ), (22407131278891/50000000000000 : ℝ), (39725400840861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(305989013/1250000000 : ℝ)|^65 ≤ (154603365819/1000000000000 : ℝ)^49
        have hw : |(305989013/1250000000 : ℝ)|=(305989013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(341272663/625000000 : ℝ)|^65 ≤ (22407131278891/50000000000000 : ℝ)^49
        have hw : |(341272663/625000000 : ℝ)|=(341272663/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4986079181/10000000000 : ℝ)|^65 ≤ (39725400840861/100000000000000 : ℝ)^49
        have hw : |(4986079181/10000000000 : ℝ)|=(4986079181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301057_s1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((48813/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(48813/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(24123/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(24123/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(57653/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(57653/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((45641/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(45641/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(91033/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(91033/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4507/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(4507/10000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (92391/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
  have base60 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (48813/50000 : ℝ) ^ (129/32 : ℝ) ≤ (90768655713679265549/100000000000000000000 : ℝ) := by
    have hpowers : (48813/50000 : ℝ)^129 ≤ (90768655713679265549/100000000000000000000 : ℝ)^32 := by
      have hnat : (48813 : ℕ)^129*100000000000000000000^32 ≤ 90768655713679265549^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48813 50000 90768655713679265549 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (48813/50000 : ℝ)) (X := (90768655713679265549/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (190768655713679265549/100000000000000000000 : ℝ) ≤ (11737703547568463/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (190768655713679265549/100000000000000000000 : ℝ)^32 ≤ (11737703547568463/10000000000000000 : ℝ)^129 := by
      have hnat : (190768655713679265549 : ℕ)^32*10000000000000000^129 ≤ 11737703547568463^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        190768655713679265549 100000000000000000000 11737703547568463 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11737703547568463/10000000000000000 : ℝ)) (X := (190768655713679265549/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (140768655713679265549/50000000000000000000 : ℝ) ≤ (12927447895769801/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (140768655713679265549/50000000000000000000 : ℝ)^32 ≤ (12927447895769801/10000000000000000 : ℝ)^129 := by
      have hnat : (140768655713679265549 : ℕ)^32*10000000000000000^129 ≤ 12927447895769801^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        140768655713679265549 50000000000000000000 12927447895769801 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12927447895769801/10000000000000000 : ℝ)) (X := (140768655713679265549/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(1737703547568463/9762600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(198290724700223/1627100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (48813/50000 : ℝ)) (alpha := (1737703547568463/9762600000000000 : ℝ)) (beta := (198290724700223/1627100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (48813/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(1737703547568463/9762600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(198290724700223/1627100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (24123/25000 : ℝ) ^ (129/32 : ℝ) ≤ (86592561362267525159/100000000000000000000 : ℝ) := by
    have hpowers : (24123/25000 : ℝ)^129 ≤ (86592561362267525159/100000000000000000000 : ℝ)^32 := by
      have hnat : (24123 : ℕ)^129*100000000000000000000^32 ≤ 86592561362267525159^32*25000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24123 25000 86592561362267525159 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24123/25000 : ℝ)) (X := (86592561362267525159/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (186592561362267525159/100000000000000000000 : ℝ) ≤ (729589558409909/625000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (186592561362267525159/100000000000000000000 : ℝ)^32 ≤ (729589558409909/625000000000000 : ℝ)^129 := by
      have hnat : (186592561362267525159 : ℕ)^32*625000000000000^129 ≤ 729589558409909^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        186592561362267525159 100000000000000000000 729589558409909 625000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (729589558409909/625000000000000 : ℝ)) (X := (186592561362267525159/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (136592561362267525159/50000000000000000000 : ℝ) ≤ (2566246734962773/2000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (136592561362267525159/50000000000000000000 : ℝ)^32 ≤ (2566246734962773/2000000000000000 : ℝ)^129 := by
      have hnat : (136592561362267525159 : ℕ)^32*2000000000000000^129 ≤ 2566246734962773^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        136592561362267525159 50000000000000000000 2566246734962773 2000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2566246734962773/2000000000000000 : ℝ)) (X := (136592561362267525159/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(104589558409909/603075000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(385933580085107/3216400000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (24123/25000 : ℝ)) (alpha := (104589558409909/603075000000000 : ℝ)) (beta := (385933580085107/3216400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (24123/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(104589558409909/603075000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(385933580085107/3216400000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (57653/100000 : ℝ) ^ (129/32 : ℝ) ≤ (10859587487125751051/100000000000000000000 : ℝ) := by
    have hpowers : (57653/100000 : ℝ)^129 ≤ (10859587487125751051/100000000000000000000 : ℝ)^32 := by
      have hnat : (57653 : ℕ)^129*100000000000000000000^32 ≤ 10859587487125751051^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57653 100000 10859587487125751051 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (57653/100000 : ℝ)) (X := (10859587487125751051/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (110859587487125751051/100000000000000000000 : ℝ) ≤ (10259035784463841/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (110859587487125751051/100000000000000000000 : ℝ)^32 ≤ (10259035784463841/10000000000000000 : ℝ)^129 := by
      have hnat : (110859587487125751051 : ℕ)^32*10000000000000000^129 ≤ 10259035784463841^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        110859587487125751051 100000000000000000000 10259035784463841 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10259035784463841/10000000000000000 : ℝ)) (X := (110859587487125751051/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (60859587487125751051/50000000000000000000 : ℝ) ≤ (1049963799006631/1000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (60859587487125751051/50000000000000000000 : ℝ)^32 ≤ (1049963799006631/1000000000000000 : ℝ)^129 := by
      have hnat : (60859587487125751051 : ℕ)^32*1000000000000000^129 ≤ 1049963799006631^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60859587487125751051 50000000000000000000 1049963799006631 1000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1049963799006631/1000000000000000 : ℝ)) (X := (60859587487125751051/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(259035784463841/5765300000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(240602205602469/5765300000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (57653/100000 : ℝ)) (alpha := (259035784463841/5765300000000000 : ℝ)) (beta := (240602205602469/5765300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (57653/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(259035784463841/5765300000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(240602205602469/5765300000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1554896093/5000000000 : ℝ)*X 0 0+(386575379/1250000000 : ℝ)*X 0 1+(1651197613/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((775181897/2500000000 : ℝ)*X 1 0+(-1541794269/5000000000 : ℝ)*X 1 1+(661890313/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5918394241/10000000000 : ℝ)*X 2 0+(1485359541/2500000000 : ℝ)*X 2 1+(6874153/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1922900361/10000000000 : ℝ)*X 0 0+(454385407/5000000000 : ℝ)*X 0 1+(4408670781/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1186048811/10000000000 : ℝ)*X 1 0+(-1658510989/10000000000 : ℝ)*X 1 1+(2209050319/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((3185304157/10000000000 : ℝ)*X 2 0+(829804717/1000000000 : ℝ)*X 2 1+(27/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((1393474913/5000000000 : ℝ)*X 0 0+(3778743387/5000000000 : ℝ)*X 0 1+(210637421/1000000000 : ℝ)*X 0 2+(1393474913/5000000000 : ℝ)*X 1 0+(3778743387/5000000000 : ℝ)*X 1 1+(210637421/1000000000 : ℝ)*X 1 2+(1393474913/5000000000 : ℝ)*X 2 0+(3778743387/5000000000 : ℝ)*X 2 1+(210637421/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-1683314961/10000000000 : ℝ)*X 0 0+(296949577/2500000000 : ℝ)*X 0 1+(8820889489/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((229455241/2500000000 : ℝ)*X 1 0+(-37575343/200000000 : ℝ)*X 1 1+(8839756211/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((8291603153/10000000000 : ℝ)*X 2 0+(1597054133/5000000000 : ℝ)*X 2 1+(33/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((7532141871/10000000000 : ℝ)*X 0 0+(2819409379/10000000000 : ℝ)*X 0 1+(52729573/250000000 : ℝ)*X 0 2+(7532141871/10000000000 : ℝ)*X 1 0+(2819409379/10000000000 : ℝ)*X 1 1+(52729573/250000000 : ℝ)*X 1 2+(7532141871/10000000000 : ℝ)*X 2 0+(2819409379/10000000000 : ℝ)*X 2 1+(52729573/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-2921971447/5000000000 : ℝ)*X 0 0+(2299620553/10000000000 : ℝ)*X 0 1+(2350072949/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((146652919/10000000000 : ℝ)*X 1 0+(-5371107997/10000000000 : ℝ)*X 1 1+(3220221017/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((1583400387/2500000000 : ℝ)*X 2 0+(341272663/625000000 : ℝ)*X 2 1+(217875681/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((305989013/1250000000 : ℝ)*X 0 0+(341272663/625000000 : ℝ)*X 0 1+(4986079181/10000000000 : ℝ)*X 0 2+(305989013/1250000000 : ℝ)*X 1 0+(341272663/625000000 : ℝ)*X 1 1+(4986079181/10000000000 : ℝ)*X 1 2+(305989013/1250000000 : ℝ)*X 2 0+(341272663/625000000 : ℝ)*X 2 1+(4986079181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301057_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((45641/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(45641/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3543744341944943958427029094311/301721466179320000000000000000000000 : ℝ) := by norm_num
    linear_combination (13336966701/125000000000 : ℝ)*(base5) + (235120660211/250000000000 : ℝ)*(base7) + (3009/62500000000 : ℝ)*(base50) + (532919/500000000000 : ℝ)*(base60) + (353156522733/200000000000 : ℝ)*(major_s1_0) + (353156522733/200000000000 : ℝ)*(major_s1_1) + (353156522733/200000000000 : ℝ)*(major_s1_2) + (2697193/500000000000 : ℝ)*(sp_s1_0) + (5408919/1000000000000 : ℝ)*(sp_s1_1) + (879282846821/500000000000 : ℝ)*(sp_s1_7) + (351679503247/200000000000 : ℝ)*(sp_s1_8) + (466316705409/250000000000 : ℝ)*(sp_s1_9) + (20274962537/10000000000 : ℝ)*(sp_s1_13) + (84081437/500000000000 : ℝ)*(sp_s1_15) + (238741869293/200000000000 : ℝ)*(f.failure) + (439642772007/250000000000 : ℝ)*(f.sum) + (6421529140461663517/9271755460000000000000000000000 : ℝ)*base62 + (1222316616009783/1153060000000000000000000000 : ℝ)*base65 + (621062021298903/643280000000000000000000000 : ℝ)*base67 + (66794558204511/1153060000000000000000000000 : ℝ)*base68 + (34355015711819356419/37522878520000000000000000000000 : ℝ)*base71 + (165218151360211/325420000000000000000000000 : ℝ)*base73 + (991907239533/40205000000000000000000000 : ℝ)*base75 + (425133609740513/650840000000000000000000000 : ℝ)*base77 + (7178805971104819397/10466808880000000000000000000000 : ℝ)*base79 + (567/5000000000000000 : ℝ)*base86 + (567/5000000000000000 : ℝ)*base88 + (567/5000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(91033/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(91033/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (15590235929222314952641079807163/1508607330896600000000000000000000000 : ℝ) := by norm_num
    linear_combination (13786580957/125000000000 : ℝ)*(base5) + (58717015359/62500000000 : ℝ)*(base7) + (381571/1000000000000 : ℝ)*(base40) + (42037/31250000000 : ℝ)*(base59) + (1761733488583/1000000000000 : ℝ)*(major_s1_0) + (1761733488583/1000000000000 : ℝ)*(major_s1_1) + (1761733488583/1000000000000 : ℝ)*(major_s1_2) + (4026309/1000000000000 : ℝ)*(sp_s1_0) + (5490063/1000000000000 : ℝ)*(sp_s1_1) + (148870199/1000000000000 : ℝ)*(sp_s1_7) + (87684002769/50000000000 : ℝ)*(sp_s1_14) + (70153098473/40000000000 : ℝ)*(sp_s1_15) + (1864125599543/1000000000000 : ℝ)*(sp_s1_16) + (2020151643587/1000000000000 : ℝ)*(sp_s1_20) + (595486022749/500000000000 : ℝ)*(f.failure) + (109614559493/62500000000 : ℝ)*(f.sum) + (3034684963717915133/27815266380000000000000000000000 : ℝ)*base62 + (493852232428537/5765300000000000000000000000 : ℝ)*base64 + (207626650033141/3216400000000000000000000000 : ℝ)*base67 + (193580110507567/5765300000000000000000000000 : ℝ)*base69 + (27563237016926166257/112568635560000000000000000000000 : ℝ)*base70 + (171435816467459/1627100000000000000000000000 : ℝ)*base73 + (294340825924477/603075000000000000000000000 : ℝ)*base75 + (3287177775745069/9762600000000000000000000000 : ℝ)*base77 + (1531911838379748327/52334044400000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (6731/12500000000000000 : ℝ)*base86 + (6731/12500000000000000 : ℝ)*base88 + (6731/12500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4507/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(4507/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (817485561652249933574797191223/377151832724150000000000000000000000 : ℝ) := by norm_num
    linear_combination (142421274857/125000000000 : ℝ)*(base5) + (109658797119/250000000000 : ℝ)*(base7) + (171593/62500000000 : ℝ)*(base40) + (1767/100000000000 : ℝ)*(base44) + (98820198931/500000000000 : ℝ)*(base50) + (187377364623/250000000000 : ℝ)*(base59) + (535274829763/500000000000 : ℝ)*(major_s1_0) + (8363669077/7812500000 : ℝ)*(major_s1_1) + (535274829763/500000000000 : ℝ)*(major_s1_2) + (20516063/500000000000 : ℝ)*(sp_s1_2) + (1147209636059/1000000000000 : ℝ)*(sp_s1_21) + (1147209618389/1000000000000 : ℝ)*(sp_s1_22) + (2286538802789/1000000000000 : ℝ)*(sp_s1_23) + (11490487221/500000000000 : ℝ)*(sp_s1_27) + (180929000623/250000000000 : ℝ)*(f.failure) + (1147209636059/1000000000000 : ℝ)*(f.sum) + (1405768917742031371/2781526638000000000000000000000 : ℝ)*base62 + (551309444924979/1441325000000000000000000000 : ℝ)*base65 + (1570816440097/12564062500000000000000000 : ℝ)*base67 + (366863522129159/1441325000000000000000000000 : ℝ)*base68 + (28858527391295316047/56284317780000000000000000000000 : ℝ)*base70 + (86943549063209/813550000000000000000000000 : ℝ)*base73 + (146469910343491/603075000000000000000000000 : ℝ)*base74 + (1153650144656291/4881300000000000000000000000 : ℝ)*base76 + (1758036827776777259/3270877775000000000000000000000 : ℝ)*base79 + (1663/6250000000000000 : ℝ)*base87 + (1663/6250000000000000 : ℝ)*base89 + (1663/6250000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((48813/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(48813/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(24123/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(24123/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(57653/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(57653/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((45641/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(45641/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(91033/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(91033/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(4507/10000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(4507/10000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301057_s1 p hpa hpb X hX hprev0

#print axioms solution
