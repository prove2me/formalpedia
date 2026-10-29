-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c306063_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:59:00.806002+00:00
-- url     : https://prove2.me/submissions/9f67aa40-5546-437e-baa9-75b539984dab

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
theorem collision_support_c306063_s2_s2_0 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-458598211/10000000000 : ℝ)*x 0 + (708390627/1250000000 : ℝ)*x 1 + (5958822291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (458598211/10000000000 : ℝ)^135 ≤ (1760218902567/100000000000000 : ℝ)^103 := by
    have hnat : (458598211 : ℕ)^135*100000000000000^103 ≤ 1760218902567^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458598211 10000000000 1760218902567 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (708390627/1250000000 : ℝ)^135 ≤ (47504816144641/100000000000000 : ℝ)^103 := by
    have hnat : (708390627 : ℕ)^135*100000000000000^103 ≤ 47504816144641^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708390627 1250000000 47504816144641 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5958822291/10000000000 : ℝ)^135 ≤ (1585467654353/3125000000000 : ℝ)^103 := by
    have hnat : (5958822291 : ℕ)^135*3125000000000^103 ≤ 1585467654353^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5958822291 10000000000 1585467654353 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-458598211/10000000000 : ℝ), (708390627/1250000000 : ℝ), (5958822291/10000000000 : ℝ)] ![(1760218902567/100000000000000 : ℝ), (47504816144641/100000000000000 : ℝ), (1585467654353/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-458598211/10000000000 : ℝ)|^135 ≤ (1760218902567/100000000000000 : ℝ)^103
        have hw : |(-458598211/10000000000 : ℝ)|=(458598211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(708390627/1250000000 : ℝ)|^135 ≤ (47504816144641/100000000000000 : ℝ)^103
        have hw : |(708390627/1250000000 : ℝ)|=(708390627/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5958822291/10000000000 : ℝ)|^135 ≤ (1585467654353/3125000000000 : ℝ)^103
        have hw : |(5958822291/10000000000 : ℝ)|=(5958822291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s2_s2_2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5734810371/10000000000 : ℝ)*x 0 + (1481650231/2500000000 : ℝ)*x 1 + (-189860979/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5734810371/10000000000 : ℝ)^135 ≤ (48249837820109/100000000000000 : ℝ)^103 := by
    have hnat : (5734810371 : ℕ)^135*100000000000000^103 ≤ 48249837820109^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5734810371 10000000000 48249837820109 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1481650231/2500000000 : ℝ)^135 ≤ (50375694047681/100000000000000 : ℝ)^103 := by
    have hnat : (1481650231 : ℕ)^135*100000000000000^103 ≤ 50375694047681^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1481650231 2500000000 50375694047681 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (189860979/5000000000 : ℝ)^135 ≤ (1374468118309/100000000000000 : ℝ)^103 := by
    have hnat : (189860979 : ℕ)^135*100000000000000^103 ≤ 1374468118309^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189860979 5000000000 1374468118309 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5734810371/10000000000 : ℝ), (1481650231/2500000000 : ℝ), (-189860979/5000000000 : ℝ)] ![(48249837820109/100000000000000 : ℝ), (50375694047681/100000000000000 : ℝ), (1374468118309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5734810371/10000000000 : ℝ)|^135 ≤ (48249837820109/100000000000000 : ℝ)^103
        have hw : |(5734810371/10000000000 : ℝ)|=(5734810371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1481650231/2500000000 : ℝ)|^135 ≤ (50375694047681/100000000000000 : ℝ)^103
        have hw : |(1481650231/2500000000 : ℝ)|=(1481650231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-189860979/5000000000 : ℝ)|^135 ≤ (1374468118309/100000000000000 : ℝ)^103
        have hw : |(-189860979/5000000000 : ℝ)|=(189860979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s2_s2_6 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (238878039/500000000 : ℝ)*x 0 + (4370364067/10000000000 : ℝ)*x 1 + (1904821513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (238878039/500000000 : ℝ)^135 ≤ (37978878330057/100000000000000 : ℝ)^103 := by
    have hnat : (238878039 : ℕ)^135*100000000000000^103 ≤ 37978878330057^103*500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238878039 500000000 37978878330057 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4370364067/10000000000 : ℝ)^135 ≤ (6758709267001/20000000000000 : ℝ)^103 := by
    have hnat : (4370364067 : ℕ)^135*20000000000000^103 ≤ 6758709267001^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4370364067 10000000000 6758709267001 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1904821513/5000000000 : ℝ)^135 ≤ (28227575313041/100000000000000 : ℝ)^103 := by
    have hnat : (1904821513 : ℕ)^135*100000000000000^103 ≤ 28227575313041^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1904821513 5000000000 28227575313041 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(238878039/500000000 : ℝ), (4370364067/10000000000 : ℝ), (1904821513/5000000000 : ℝ)] ![(37978878330057/100000000000000 : ℝ), (6758709267001/20000000000000 : ℝ), (28227575313041/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(238878039/500000000 : ℝ)|^135 ≤ (37978878330057/100000000000000 : ℝ)^103
        have hw : |(238878039/500000000 : ℝ)|=(238878039/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4370364067/10000000000 : ℝ)|^135 ≤ (6758709267001/20000000000000 : ℝ)^103
        have hw : |(4370364067/10000000000 : ℝ)|=(4370364067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1904821513/5000000000 : ℝ)|^135 ≤ (28227575313041/100000000000000 : ℝ)^103
        have hw : |(1904821513/5000000000 : ℝ)|=(1904821513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s2_s2_7 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-882660007/10000000000 : ℝ)*x 0 + (2518041533/10000000000 : ℝ)*x 1 + (8389654849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (882660007/10000000000 : ℝ)^135 ≤ (1038037340231/25000000000000 : ℝ)^103 := by
    have hnat : (882660007 : ℕ)^135*25000000000000^103 ≤ 1038037340231^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882660007 10000000000 1038037340231 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2518041533/10000000000 : ℝ)^135 ≤ (16405343951483/100000000000000 : ℝ)^103 := by
    have hnat : (2518041533 : ℕ)^135*100000000000000^103 ≤ 16405343951483^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2518041533 10000000000 16405343951483 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8389654849/10000000000 : ℝ)^135 ≤ (7944250667153/10000000000000 : ℝ)^103 := by
    have hnat : (8389654849 : ℕ)^135*10000000000000^103 ≤ 7944250667153^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8389654849 10000000000 7944250667153 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-882660007/10000000000 : ℝ), (2518041533/10000000000 : ℝ), (8389654849/10000000000 : ℝ)] ![(1038037340231/25000000000000 : ℝ), (16405343951483/100000000000000 : ℝ), (7944250667153/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-882660007/10000000000 : ℝ)|^135 ≤ (1038037340231/25000000000000 : ℝ)^103
        have hw : |(-882660007/10000000000 : ℝ)|=(882660007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2518041533/10000000000 : ℝ)|^135 ≤ (16405343951483/100000000000000 : ℝ)^103
        have hw : |(2518041533/10000000000 : ℝ)|=(2518041533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8389654849/10000000000 : ℝ)|^135 ≤ (7944250667153/10000000000000 : ℝ)^103
        have hw : |(8389654849/10000000000 : ℝ)|=(8389654849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s2_s2_8 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2944233829/10000000000 : ℝ)*x 0 + (-27617557/2000000000 : ℝ)*x 1 + (2098532483/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2944233829/10000000000 : ℝ)^135 ≤ (629278421937/3125000000000 : ℝ)^103 := by
    have hnat : (2944233829 : ℕ)^135*3125000000000^103 ≤ 629278421937^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2944233829 10000000000 629278421937 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27617557/2000000000 : ℝ)^135 ≤ (1825195659/500000000000 : ℝ)^103 := by
    have hnat : (27617557 : ℕ)^135*500000000000^103 ≤ 1825195659^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27617557 2000000000 1825195659 500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2098532483/2500000000 : ℝ)^135 ≤ (79498051350697/100000000000000 : ℝ)^103 := by
    have hnat : (2098532483 : ℕ)^135*100000000000000^103 ≤ 79498051350697^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098532483 2500000000 79498051350697 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2944233829/10000000000 : ℝ), (-27617557/2000000000 : ℝ), (2098532483/2500000000 : ℝ)] ![(629278421937/3125000000000 : ℝ), (1825195659/500000000000 : ℝ), (79498051350697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2944233829/10000000000 : ℝ)|^135 ≤ (629278421937/3125000000000 : ℝ)^103
        have hw : |(2944233829/10000000000 : ℝ)|=(2944233829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-27617557/2000000000 : ℝ)|^135 ≤ (1825195659/500000000000 : ℝ)^103
        have hw : |(-27617557/2000000000 : ℝ)|=(27617557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2098532483/2500000000 : ℝ)|^135 ≤ (79498051350697/100000000000000 : ℝ)^103
        have hw : |(2098532483/2500000000 : ℝ)|=(2098532483/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s2_s2_9 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1501206659/5000000000 : ℝ)*x 0 + (4187894023/5000000000 : ℝ)*x 1 + (-2434809/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1501206659/5000000000 : ℝ)^135 ≤ (2582505302033/12500000000000 : ℝ)^103 := by
    have hnat : (1501206659 : ℕ)^135*12500000000000^103 ≤ 2582505302033^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1501206659 5000000000 2582505302033 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4187894023/5000000000 : ℝ)^135 ≤ (79270450533151/100000000000000 : ℝ)^103 := by
    have hnat : (4187894023 : ℕ)^135*100000000000000^103 ≤ 79270450533151^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4187894023 5000000000 79270450533151 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2434809/625000000 : ℝ)^135 ≤ (69507029341/100000000000000 : ℝ)^103 := by
    have hnat : (2434809 : ℕ)^135*100000000000000^103 ≤ 69507029341^103*625000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2434809 625000000 69507029341 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1501206659/5000000000 : ℝ), (4187894023/5000000000 : ℝ), (-2434809/625000000 : ℝ)] ![(2582505302033/12500000000000 : ℝ), (79270450533151/100000000000000 : ℝ), (69507029341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1501206659/5000000000 : ℝ)|^135 ≤ (2582505302033/12500000000000 : ℝ)^103
        have hw : |(1501206659/5000000000 : ℝ)|=(1501206659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4187894023/5000000000 : ℝ)|^135 ≤ (79270450533151/100000000000000 : ℝ)^103
        have hw : |(4187894023/5000000000 : ℝ)|=(4187894023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2434809/625000000 : ℝ)|^135 ≤ (69507029341/100000000000000 : ℝ)^103
        have hw : |(-2434809/625000000 : ℝ)|=(2434809/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s2_s2_13 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3114687143/10000000000 : ℝ)*x 0 + (7435301587/10000000000 : ℝ)*x 1 + (1792541387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3114687143/10000000000 : ℝ)^135 ≤ (21678469714697/100000000000000 : ℝ)^103 := by
    have hnat : (3114687143 : ℕ)^135*100000000000000^103 ≤ 21678469714697^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3114687143 10000000000 21678469714697 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7435301587/10000000000 : ℝ)^135 ≤ (67813113475373/100000000000000 : ℝ)^103 := by
    have hnat : (7435301587 : ℕ)^135*100000000000000^103 ≤ 67813113475373^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7435301587 10000000000 67813113475373 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1792541387/10000000000 : ℝ)^135 ≤ (656776049917/6250000000000 : ℝ)^103 := by
    have hnat : (1792541387 : ℕ)^135*6250000000000^103 ≤ 656776049917^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1792541387 10000000000 656776049917 6250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3114687143/10000000000 : ℝ), (7435301587/10000000000 : ℝ), (1792541387/10000000000 : ℝ)] ![(21678469714697/100000000000000 : ℝ), (67813113475373/100000000000000 : ℝ), (656776049917/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3114687143/10000000000 : ℝ)|^135 ≤ (21678469714697/100000000000000 : ℝ)^103
        have hw : |(3114687143/10000000000 : ℝ)|=(3114687143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7435301587/10000000000 : ℝ)|^135 ≤ (67813113475373/100000000000000 : ℝ)^103
        have hw : |(7435301587/10000000000 : ℝ)|=(7435301587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1792541387/10000000000 : ℝ)|^135 ≤ (656776049917/6250000000000 : ℝ)^103
        have hw : |(1792541387/10000000000 : ℝ)|=(1792541387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s2_s2_14 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-53945723/5000000000 : ℝ)*x 0 + (2870645569/10000000000 : ℝ)*x 1 + (67640987/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53945723/5000000000 : ℝ)^135 ≤ (264165551623/100000000000000 : ℝ)^103 := by
    have hnat : (53945723 : ℕ)^135*100000000000000^103 ≤ 264165551623^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53945723 5000000000 264165551623 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2870645569/10000000000 : ℝ)^135 ≤ (608744290643/3125000000000 : ℝ)^103 := by
    have hnat : (2870645569 : ℕ)^135*3125000000000^103 ≤ 608744290643^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2870645569 10000000000 608744290643 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (67640987/80000000 : ℝ)^135 ≤ (3210240685247/4000000000000 : ℝ)^103 := by
    have hnat : (67640987 : ℕ)^135*4000000000000^103 ≤ 3210240685247^103*80000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      67640987 80000000 3210240685247 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53945723/5000000000 : ℝ), (2870645569/10000000000 : ℝ), (67640987/80000000 : ℝ)] ![(264165551623/100000000000000 : ℝ), (608744290643/3125000000000 : ℝ), (3210240685247/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53945723/5000000000 : ℝ)|^135 ≤ (264165551623/100000000000000 : ℝ)^103
        have hw : |(-53945723/5000000000 : ℝ)|=(53945723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2870645569/10000000000 : ℝ)|^135 ≤ (608744290643/3125000000000 : ℝ)^103
        have hw : |(2870645569/10000000000 : ℝ)|=(2870645569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(67640987/80000000 : ℝ)|^135 ≤ (3210240685247/4000000000000 : ℝ)^103
        have hw : |(67640987/80000000 : ℝ)|=(67640987/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s2_s2_15 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1215855281/5000000000 : ℝ)*x 0 + (-215107887/2500000000 : ℝ)*x 1 + (1691928793/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1215855281/5000000000 : ℝ)^135 ≤ (15672101035887/100000000000000 : ℝ)^103 := by
    have hnat : (1215855281 : ℕ)^135*100000000000000^103 ≤ 15672101035887^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1215855281 5000000000 15672101035887 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215107887/2500000000 : ℝ)^135 ≤ (125488644727/3125000000000 : ℝ)^103 := by
    have hnat : (215107887 : ℕ)^135*3125000000000^103 ≤ 125488644727^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215107887 2500000000 125488644727 3125000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1691928793/2000000000 : ℝ)^135 ≤ (80312262320323/100000000000000 : ℝ)^103 := by
    have hnat : (1691928793 : ℕ)^135*100000000000000^103 ≤ 80312262320323^103*2000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1691928793 2000000000 80312262320323 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1215855281/5000000000 : ℝ), (-215107887/2500000000 : ℝ), (1691928793/2000000000 : ℝ)] ![(15672101035887/100000000000000 : ℝ), (125488644727/3125000000000 : ℝ), (80312262320323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1215855281/5000000000 : ℝ)|^135 ≤ (15672101035887/100000000000000 : ℝ)^103
        have hw : |(1215855281/5000000000 : ℝ)|=(1215855281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-215107887/2500000000 : ℝ)|^135 ≤ (125488644727/3125000000000 : ℝ)^103
        have hw : |(-215107887/2500000000 : ℝ)|=(215107887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1691928793/2000000000 : ℝ)|^135 ≤ (80312262320323/100000000000000 : ℝ)^103
        have hw : |(1691928793/2000000000 : ℝ)|=(1691928793/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s2_s2_16 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2052942403/2500000000 : ℝ)*x 0 + (1609600597/5000000000 : ℝ)*x 1 + (-29749911/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2052942403/2500000000 : ℝ)^135 ≤ (19310521822549/25000000000000 : ℝ)^103 := by
    have hnat : (2052942403 : ℕ)^135*25000000000000^103 ≤ 19310521822549^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052942403 2500000000 19310521822549 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1609600597/5000000000 : ℝ)^135 ≤ (4527364831249/20000000000000 : ℝ)^103 := by
    have hnat : (1609600597 : ℕ)^135*20000000000000^103 ≤ 4527364831249^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1609600597 5000000000 4527364831249 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (29749911/5000000000 : ℝ)^135 ≤ (60544272121/50000000000000 : ℝ)^103 := by
    have hnat : (29749911 : ℕ)^135*50000000000000^103 ≤ 60544272121^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29749911 5000000000 60544272121 50000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2052942403/2500000000 : ℝ), (1609600597/5000000000 : ℝ), (-29749911/5000000000 : ℝ)] ![(19310521822549/25000000000000 : ℝ), (4527364831249/20000000000000 : ℝ), (60544272121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2052942403/2500000000 : ℝ)|^135 ≤ (19310521822549/25000000000000 : ℝ)^103
        have hw : |(2052942403/2500000000 : ℝ)|=(2052942403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1609600597/5000000000 : ℝ)|^135 ≤ (4527364831249/20000000000000 : ℝ)^103
        have hw : |(1609600597/5000000000 : ℝ)|=(1609600597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-29749911/5000000000 : ℝ)|^135 ≤ (60544272121/50000000000000 : ℝ)^103
        have hw : |(-29749911/5000000000 : ℝ)|=(29749911/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s2_s2_20 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3846186907/5000000000 : ℝ)*x 0 + (1388847971/5000000000 : ℝ)*x 1 + (891826669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3846186907/5000000000 : ℝ)^135 ≤ (14180503774781/20000000000000 : ℝ)^103 := by
    have hnat : (3846186907 : ℕ)^135*20000000000000^103 ≤ 14180503774781^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3846186907 5000000000 14180503774781 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1388847971/5000000000 : ℝ)^135 ≤ (18657303845423/100000000000000 : ℝ)^103 := by
    have hnat : (1388847971 : ℕ)^135*100000000000000^103 ≤ 18657303845423^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1388847971 5000000000 18657303845423 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (891826669/5000000000 : ℝ)^135 ≤ (10440177262699/100000000000000 : ℝ)^103 := by
    have hnat : (891826669 : ℕ)^135*100000000000000^103 ≤ 10440177262699^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891826669 5000000000 10440177262699 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3846186907/5000000000 : ℝ), (1388847971/5000000000 : ℝ), (891826669/5000000000 : ℝ)] ![(14180503774781/20000000000000 : ℝ), (18657303845423/100000000000000 : ℝ), (10440177262699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3846186907/5000000000 : ℝ)|^135 ≤ (14180503774781/20000000000000 : ℝ)^103
        have hw : |(3846186907/5000000000 : ℝ)|=(3846186907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1388847971/5000000000 : ℝ)|^135 ≤ (18657303845423/100000000000000 : ℝ)^103
        have hw : |(1388847971/5000000000 : ℝ)|=(1388847971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(891826669/5000000000 : ℝ)|^135 ≤ (10440177262699/100000000000000 : ℝ)^103
        have hw : |(891826669/5000000000 : ℝ)|=(891826669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s2_s2_21 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-20102809/1250000000 : ℝ)*x 0 + (7639217603/10000000000 : ℝ)*x 1 + (3918888769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20102809/1250000000 : ℝ)^135 ≤ (445753983599/100000000000000 : ℝ)^103 := by
    have hnat : (20102809 : ℕ)^135*100000000000000^103 ≤ 445753983599^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20102809 1250000000 445753983599 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7639217603/10000000000 : ℝ)^135 ≤ (702610365961/1000000000000 : ℝ)^103 := by
    have hnat : (7639217603 : ℕ)^135*1000000000000^103 ≤ 702610365961^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7639217603 10000000000 702610365961 1000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3918888769/10000000000 : ℝ)^135 ≤ (7323302351027/25000000000000 : ℝ)^103 := by
    have hnat : (3918888769 : ℕ)^135*25000000000000^103 ≤ 7323302351027^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3918888769 10000000000 7323302351027 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-20102809/1250000000 : ℝ), (7639217603/10000000000 : ℝ), (3918888769/10000000000 : ℝ)] ![(445753983599/100000000000000 : ℝ), (702610365961/1000000000000 : ℝ), (7323302351027/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-20102809/1250000000 : ℝ)|^135 ≤ (445753983599/100000000000000 : ℝ)^103
        have hw : |(-20102809/1250000000 : ℝ)|=(20102809/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7639217603/10000000000 : ℝ)|^135 ≤ (702610365961/1000000000000 : ℝ)^103
        have hw : |(7639217603/10000000000 : ℝ)|=(7639217603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3918888769/10000000000 : ℝ)|^135 ≤ (7323302351027/25000000000000 : ℝ)^103
        have hw : |(3918888769/10000000000 : ℝ)|=(3918888769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s2_s2_22 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (8143388863/10000000000 : ℝ)*x 0 + (-1453833/312500000 : ℝ)*x 1 + (828436683/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8143388863/10000000000 : ℝ)^135 ≤ (76400140935483/100000000000000 : ℝ)^103 := by
    have hnat : (8143388863 : ℕ)^135*100000000000000^103 ≤ 76400140935483^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8143388863 10000000000 76400140935483 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1453833/312500000 : ℝ)^135 ≤ (10963909113/12500000000000 : ℝ)^103 := by
    have hnat : (1453833 : ℕ)^135*12500000000000^103 ≤ 10963909113^103*312500000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1453833 312500000 10963909113 12500000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (828436683/2500000000 : ℝ)^135 ≤ (146950923621/625000000000 : ℝ)^103 := by
    have hnat : (828436683 : ℕ)^135*625000000000^103 ≤ 146950923621^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      828436683 2500000000 146950923621 625000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8143388863/10000000000 : ℝ), (-1453833/312500000 : ℝ), (828436683/2500000000 : ℝ)] ![(76400140935483/100000000000000 : ℝ), (10963909113/12500000000000 : ℝ), (146950923621/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8143388863/10000000000 : ℝ)|^135 ≤ (76400140935483/100000000000000 : ℝ)^103
        have hw : |(8143388863/10000000000 : ℝ)|=(8143388863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1453833/312500000 : ℝ)|^135 ≤ (10963909113/12500000000000 : ℝ)^103
        have hw : |(-1453833/312500000 : ℝ)|=(1453833/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(828436683/2500000000 : ℝ)|^135 ≤ (146950923621/625000000000 : ℝ)^103
        have hw : |(828436683/2500000000 : ℝ)|=(828436683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s2_s2_23 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2292036593/10000000000 : ℝ)*x 0 + (2150173297/2500000000 : ℝ)*x 1 + (-95264391/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2292036593/10000000000 : ℝ)^135 ≤ (2900583828377/20000000000000 : ℝ)^103 := by
    have hnat : (2292036593 : ℕ)^135*20000000000000^103 ≤ 2900583828377^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2292036593 10000000000 2900583828377 20000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2150173297/2500000000 : ℝ)^135 ≤ (3282874844057/4000000000000 : ℝ)^103 := by
    have hnat : (2150173297 : ℕ)^135*4000000000000^103 ≤ 3282874844057^103*2500000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2150173297 2500000000 3282874844057 4000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (95264391/1250000000 : ℝ)^135 ≤ (856302436721/25000000000000 : ℝ)^103 := by
    have hnat : (95264391 : ℕ)^135*25000000000000^103 ≤ 856302436721^103*1250000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95264391 1250000000 856302436721 25000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2292036593/10000000000 : ℝ), (2150173297/2500000000 : ℝ), (-95264391/1250000000 : ℝ)] ![(2900583828377/20000000000000 : ℝ), (3282874844057/4000000000000 : ℝ), (856302436721/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2292036593/10000000000 : ℝ)|^135 ≤ (2900583828377/20000000000000 : ℝ)^103
        have hw : |(2292036593/10000000000 : ℝ)|=(2292036593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2150173297/2500000000 : ℝ)|^135 ≤ (3282874844057/4000000000000 : ℝ)^103
        have hw : |(2150173297/2500000000 : ℝ)|=(2150173297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-95264391/1250000000 : ℝ)|^135 ≤ (856302436721/25000000000000 : ℝ)^103
        have hw : |(-95264391/1250000000 : ℝ)|=(95264391/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c306063_s2_s2_27 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ)) (x : Fin 3 → ℝ) :
    (3911063943/5000000000 : ℝ)*x 0 + (2542515173/10000000000 : ℝ)*x 1 + (184472861/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3911063943/5000000000 : ℝ)^135 ≤ (72474151111967/100000000000000 : ℝ)^103 := by
    have hnat : (3911063943 : ℕ)^135*100000000000000^103 ≤ 72474151111967^103*5000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3911063943 5000000000 72474151111967 100000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2542515173/10000000000 : ℝ)^135 ≤ (207683061921/1250000000000 : ℝ)^103 := by
    have hnat : (2542515173 : ℕ)^135*1250000000000^103 ≤ 207683061921^103*10000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542515173 10000000000 207683061921 1250000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (184472861/1000000000 : ℝ)^135 ≤ (1091120391761/10000000000000 : ℝ)^103 := by
    have hnat : (184472861 : ℕ)^135*10000000000000^103 ≤ 1091120391761^103*1000000000^135 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      184472861 1000000000 1091120391761 10000000000000 135 103 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (135/32 : ℝ)) 135 103 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3911063943/5000000000 : ℝ), (2542515173/10000000000 : ℝ), (184472861/1000000000 : ℝ)] ![(72474151111967/100000000000000 : ℝ), (207683061921/1250000000000 : ℝ), (1091120391761/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3911063943/5000000000 : ℝ)|^135 ≤ (72474151111967/100000000000000 : ℝ)^103
        have hw : |(3911063943/5000000000 : ℝ)|=(3911063943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2542515173/10000000000 : ℝ)|^135 ≤ (207683061921/1250000000000 : ℝ)^103
        have hw : |(2542515173/10000000000 : ℝ)|=(2542515173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(184472861/1000000000 : ℝ)|^135 ≤ (1091120391761/10000000000000 : ℝ)^103
        have hw : |(184472861/1000000000 : ℝ)|=(184472861/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c306063_s2 (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((5431/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5431/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21663/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21663/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5253/6250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5253/6250 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((15759/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15759/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(78903/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(78903/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76081/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(76081/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (38461/50000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (38461/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (38461/50000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (38461/50000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (92997/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s2_pow0 : (5431/6250 : ℝ) ^ (67/16 : ℝ) ≤ (13883584575495817329/25000000000000000000 : ℝ) := by
    have hpowers : (5431/6250 : ℝ)^67 ≤ (13883584575495817329/25000000000000000000 : ℝ)^16 := by
      have hnat : (5431 : ℕ)^67*25000000000000000000^16 ≤ 13883584575495817329^16*6250^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5431 6250 13883584575495817329 25000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5431/6250 : ℝ)) (X := (13883584575495817329/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (38883584575495817329/25000000000000000000 : ℝ) ≤ (2778108933189953/2500000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (38883584575495817329/25000000000000000000 : ℝ)^16 ≤ (2778108933189953/2500000000000000 : ℝ)^67 := by
      have hnat : (38883584575495817329 : ℕ)^16*2500000000000000^67 ≤ 2778108933189953^67*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38883584575495817329 25000000000000000000 2778108933189953 2500000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2778108933189953/2500000000000000 : ℝ)) (X := (38883584575495817329/25000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (26383584575495817329/12500000000000000000 : ℝ) ≤ (11952928928677937/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (26383584575495817329/12500000000000000000 : ℝ)^16 ≤ (11952928928677937/10000000000000000 : ℝ)^67 := by
      have hnat : (26383584575495817329 : ℕ)^16*10000000000000000^67 ≤ 11952928928677937^67*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26383584575495817329 12500000000000000000 11952928928677937 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11952928928677937/10000000000000000 : ℝ)) (X := (26383584575495817329/12500000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(278108933189953/2172400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1344789113469/13903360000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (5431/6250 : ℝ)) (alpha := (278108933189953/2172400000000000 : ℝ)) (beta := (1344789113469/13903360000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (5431/6250 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(278108933189953/2172400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1344789113469/13903360000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (21663/25000 : ℝ) ^ (67/16 : ℝ) ≤ (54884264671478297567/100000000000000000000 : ℝ) := by
    have hpowers : (21663/25000 : ℝ)^67 ≤ (54884264671478297567/100000000000000000000 : ℝ)^16 := by
      have hnat : (21663 : ℕ)^67*100000000000000000000^16 ≤ 54884264671478297567^16*25000^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21663 25000 54884264671478297567 100000000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21663/25000 : ℝ)) (X := (54884264671478297567/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (154884264671478297567/100000000000000000000 : ℝ) ≤ (555066326737051/500000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (154884264671478297567/100000000000000000000 : ℝ)^16 ≤ (555066326737051/500000000000000 : ℝ)^67 := by
      have hnat : (154884264671478297567 : ℕ)^16*500000000000000^67 ≤ 555066326737051^67*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        154884264671478297567 100000000000000000000 555066326737051 500000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (555066326737051/500000000000000 : ℝ)) (X := (154884264671478297567/100000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (104884264671478297567/50000000000000000000 : ℝ) ≤ (11935304747917873/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (104884264671478297567/50000000000000000000 : ℝ)^16 ≤ (11935304747917873/10000000000000000 : ℝ)^67 := by
      have hnat : (104884264671478297567 : ℕ)^16*10000000000000000^67 ≤ 11935304747917873^67*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104884264671478297567 50000000000000000000 11935304747917873 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11935304747917873/10000000000000000 : ℝ)) (X := (104884264671478297567/50000000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(55066326737051/433260000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(833978213176853/8665200000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (21663/25000 : ℝ)) (alpha := (55066326737051/433260000000000 : ℝ)) (beta := (833978213176853/8665200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (21663/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(55066326737051/433260000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(833978213176853/8665200000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (5253/6250 : ℝ) ^ (67/16 : ℝ) ≤ (1207531383804402777/2500000000000000000 : ℝ) := by
    have hpowers : (5253/6250 : ℝ)^67 ≤ (1207531383804402777/2500000000000000000 : ℝ)^16 := by
      have hnat : (5253 : ℕ)^67*2500000000000000000^16 ≤ 1207531383804402777^16*6250^67 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5253 6250 1207531383804402777 2500000000000000000 67 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5253/6250 : ℝ)) (X := (1207531383804402777/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (3707531383804402777/2500000000000000000 : ℝ) ≤ (1373347431240727/1250000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (3707531383804402777/2500000000000000000 : ℝ)^16 ≤ (1373347431240727/1250000000000000 : ℝ)^67 := by
      have hnat : (3707531383804402777 : ℕ)^16*1250000000000000^67 ≤ 1373347431240727^67*2500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3707531383804402777 2500000000000000000 1373347431240727 1250000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1373347431240727/1250000000000000 : ℝ)) (X := (3707531383804402777/2500000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (2457531383804402777/1250000000000000000 : ℝ) ≤ (11751973953116689/10000000000000000 : ℝ) ^ (67/16 : ℝ) := by
    have hpowers : (2457531383804402777/1250000000000000000 : ℝ)^16 ≤ (11751973953116689/10000000000000000 : ℝ)^67 := by
      have hnat : (2457531383804402777 : ℕ)^16*10000000000000000^67 ≤ 11751973953116689^67*1250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2457531383804402777 1250000000000000000 11751973953116689 10000000000000000 16 67 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11751973953116689/10000000000000000 : ℝ)) (X := (2457531383804402777/1250000000000000000 : ℝ)) (by norm_num) 67 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(123347431240727/1050600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(45011441364169/494400000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (67/16 : ℝ)) (rho := (5253/6250 : ℝ)) (alpha := (123347431240727/1050600000000000 : ℝ)) (beta := (45011441364169/494400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (5253/6250 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(123347431240727/1050600000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(45011441364169/494400000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-458598211/10000000000 : ℝ)*X 0 0+(708390627/1250000000 : ℝ)*X 0 1+(5958822291/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((5734810371/10000000000 : ℝ)*X 2 0+(1481650231/2500000000 : ℝ)*X 2 1+(-189860979/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((238878039/500000000 : ℝ)*X 0 0+(4370364067/10000000000 : ℝ)*X 0 1+(1904821513/5000000000 : ℝ)*X 0 2+(238878039/500000000 : ℝ)*X 1 0+(4370364067/10000000000 : ℝ)*X 1 1+(1904821513/5000000000 : ℝ)*X 1 2+(238878039/500000000 : ℝ)*X 2 0+(4370364067/10000000000 : ℝ)*X 2 1+(1904821513/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-882660007/10000000000 : ℝ)*X 0 0+(2518041533/10000000000 : ℝ)*X 0 1+(8389654849/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((2944233829/10000000000 : ℝ)*X 1 0+(-27617557/2000000000 : ℝ)*X 1 1+(2098532483/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((1501206659/5000000000 : ℝ)*X 2 0+(4187894023/5000000000 : ℝ)*X 2 1+(-2434809/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((3114687143/10000000000 : ℝ)*X 0 0+(7435301587/10000000000 : ℝ)*X 0 1+(1792541387/10000000000 : ℝ)*X 0 2+(3114687143/10000000000 : ℝ)*X 1 0+(7435301587/10000000000 : ℝ)*X 1 1+(1792541387/10000000000 : ℝ)*X 1 2+(3114687143/10000000000 : ℝ)*X 2 0+(7435301587/10000000000 : ℝ)*X 2 1+(1792541387/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-53945723/5000000000 : ℝ)*X 0 0+(2870645569/10000000000 : ℝ)*X 0 1+(67640987/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((1215855281/5000000000 : ℝ)*X 1 0+(-215107887/2500000000 : ℝ)*X 1 1+(1691928793/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((2052942403/2500000000 : ℝ)*X 2 0+(1609600597/5000000000 : ℝ)*X 2 1+(-29749911/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((3846186907/5000000000 : ℝ)*X 0 0+(1388847971/5000000000 : ℝ)*X 0 1+(891826669/5000000000 : ℝ)*X 0 2+(3846186907/5000000000 : ℝ)*X 1 0+(1388847971/5000000000 : ℝ)*X 1 1+(891826669/5000000000 : ℝ)*X 1 2+(3846186907/5000000000 : ℝ)*X 2 0+(1388847971/5000000000 : ℝ)*X 2 1+(891826669/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-20102809/1250000000 : ℝ)*X 0 0+(7639217603/10000000000 : ℝ)*X 0 1+(3918888769/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((8143388863/10000000000 : ℝ)*X 1 0+(-1453833/312500000 : ℝ)*X 1 1+(828436683/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((2292036593/10000000000 : ℝ)*X 2 0+(2150173297/2500000000 : ℝ)*X 2 1+(-95264391/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((3911063943/5000000000 : ℝ)*X 0 0+(2542515173/10000000000 : ℝ)*X 0 1+(184472861/1000000000 : ℝ)*X 0 2+(3911063943/5000000000 : ℝ)*X 1 0+(2542515173/10000000000 : ℝ)*X 1 1+(184472861/1000000000 : ℝ)*X 1 2+(3911063943/5000000000 : ℝ)*X 2 0+(2542515173/10000000000 : ℝ)*X 2 1+(184472861/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c306063_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((15759/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15759/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (14139008534210902067786323201/1615750741200000000000000000000000 : ℝ) := by norm_num
    linear_combination (768273405551/1000000000000 : ℝ)*(base7) + (547457/500000000000 : ℝ)*(base50) + (1177079939/200000000000 : ℝ)*(base60) + (1702629355031/1000000000000 : ℝ)*(major_s2_0) + (1702629355031/1000000000000 : ℝ)*(major_s2_1) + (1702629355031/1000000000000 : ℝ)*(major_s2_2) + (333567/62500000000 : ℝ)*(sp_s2_0) + (636467/1000000000000 : ℝ)*(sp_s2_6) + (912305874407/500000000000 : ℝ)*(sp_s2_7) + (456167894549/250000000000 : ℝ)*(sp_s2_8) + (912335949139/500000000000 : ℝ)*(sp_s2_9) + (1872542517979/1000000000000 : ℝ)*(sp_s2_13) + (6851549/125000000000 : ℝ)*(sp_s2_14) + (160041/500000000000 : ℝ)*(sp_s2_15) + (220853949779/200000000000 : ℝ)*(f.failure) + (912335949139/500000000000 : ℝ)*(f.sum) + (26803824416221111/446257800000000000000000000000 : ℝ)*base63 + (70260212497679/494400000000000000000000000 : ℝ)*base65 + (6801225320828117/8665200000000000000000000000 : ℝ)*base66 + (37516865263939/61800000000000000000000000 : ℝ)*base68 + (1275181215756006917/2685086400000000000000000000000 : ℝ)*base71 + (829286069276689/1737920000000000000000000000 : ℝ)*base72 + (311025638219/86652000000000000000000000 : ℝ)*base75 + (974191699246457/2172400000000000000000000000 : ℝ)*base76 + (32866095853364484983/188242804800000000000000000000000 : ℝ)*base78 + (2447/10000000000000000 : ℝ)*base87 + (2447/10000000000000000 : ℝ)*base89 + (2447/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(78903/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(78903/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (79594334168480472859904408911/18311841733600000000000000000000000 : ℝ) := by norm_num
    linear_combination (155327669757/200000000000 : ℝ)*(base7) + (1504939/1000000000000 : ℝ)*(base53) + (137651/500000000000 : ℝ)*(base60) + (828517424889/500000000000 : ℝ)*(major_s2_0) + (828517424889/500000000000 : ℝ)*(major_s2_1) + (1657033344839/1000000000000 : ℝ)*(major_s2_2) + (184159/200000000000 : ℝ)*(sp_s2_6) + (1547129/1000000000000 : ℝ)*(sp_s2_7) + (19984377/1000000000000 : ℝ)*(sp_s2_8) + (878933156041/500000000000 : ℝ)*(sp_s2_14) + (878923937417/500000000000 : ℝ)*(sp_s2_15) + (35157387283/20000000000 : ℝ)*(sp_s2_16) + (231408271171/125000000000 : ℝ)*(sp_s2_20) + (17475419/250000000000 : ℝ)*(sp_s2_27) + (1074698643053/1000000000000 : ℝ)*(f.failure) + (35157387283/20000000000 : ℝ)*(f.sum) + (628712685653521443/842931400000000000000000000000 : ℝ)*base62 + (81715584992831/494400000000000000000000000 : ℝ)*base65 + (122131634116261/1444200000000000000000000000 : ℝ)*base66 + (786783233356787/1050600000000000000000000000 : ℝ)*base68 + (88764291557821693/537017280000000000000000000000 : ℝ)*base71 + (71110292852223/868960000000000000000000000 : ℝ)*base72 + (3473524492727/14442000000000000000000000 : ℝ)*base74 + (242764021552563/1086200000000000000000000000 : ℝ)*base76 + (4309052187123572659/31373800800000000000000000000000 : ℝ)*base78 + (15071/50000000000000000 : ℝ)*base86 + (15071/50000000000000000 : ℝ)*base88 + (15071/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76081/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(76081/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8551691114209287463052585791/915592086680000000000000000000000 : ℝ) := by norm_num
    linear_combination (96903339351/125000000000 : ℝ)*(base7) + (102580223493/1000000000000 : ℝ)*(base40) + (7532531/1000000000000 : ℝ)*(base43) + (576059/1000000000000 : ℝ)*(base49) + (209373/200000000000 : ℝ)*(base59) + (800311631473/500000000000 : ℝ)*(major_s2_0) + (320123146083/200000000000 : ℝ)*(major_s2_1) + (800311631473/500000000000 : ℝ)*(major_s2_2) + (4231321/500000000000 : ℝ)*(sp_s2_2) + (5739301/125000000000 : ℝ)*(sp_s2_9) + (841249444849/500000000000 : ℝ)*(sp_s2_21) + (1682506422229/1000000000000 : ℝ)*(sp_s2_22) + (210305564081/125000000000 : ℝ)*(sp_s2_23) + (906669323233/500000000000 : ℝ)*(sp_s2_27) + (519055965829/500000000000 : ℝ)*(f.failure) + (1682506422229/1000000000000 : ℝ)*(f.sum) + (147951408831680089/632198550000000000000000000000 : ℝ)*base62 + (36669108805703/247200000000000000000000000 : ℝ)*base64 + (5014493723963/577680000000000000000000000 : ℝ)*base66 + (228380064401719/525300000000000000000000000 : ℝ)*base68 + (272404336346292749/1342543200000000000000000000000 : ℝ)*base70 + (88009375753977/868960000000000000000000000 : ℝ)*base73 + (53880359701117/144420000000000000000000000 : ℝ)*base74 + (749112128372391/1086200000000000000000000000 : ℝ)*base76 + (2443385028143706323/6274760160000000000000000000000 : ℝ)*base79 + (5097/25000000000000000 : ℝ)*base87 + (5097/25000000000000000 : ℝ)*base89 + (5097/25000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (67/16 : ℝ) ≤ p) (hpb : p ≤ (135/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (77093/50000 : ℝ) (92997/50000 : ℝ) (38461/50000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((5431/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5431/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21663/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21663/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5253/6250 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5253/6250 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((15759/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(15759/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(78903/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(78903/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76081/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(76081/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c306063_s2 p hpa hpb X hX hprev1

#print axioms solution
