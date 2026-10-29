-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c309086_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:06:54.494348+00:00
-- url     : https://prove2.me/submissions/aa013664-9e71-47d9-984d-b295d640df0d

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
theorem collision_support_c309086_s2_s2_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6180014883/10000000000 : ℝ)*x 0 + (830825909/2500000000 : ℝ)*x 1 + (126282701/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6180014883/10000000000 : ℝ)^35 ≤ (53587129046987/100000000000000 : ℝ)^27 := by
    have hnat : (6180014883 : ℕ)^35*100000000000000^27 ≤ 53587129046987^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6180014883 10000000000 53587129046987 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (830825909/2500000000 : ℝ)^35 ≤ (23978002017881/100000000000000 : ℝ)^27 := by
    have hnat : (830825909 : ℕ)^35*100000000000000^27 ≤ 23978002017881^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830825909 2500000000 23978002017881 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126282701/400000000 : ℝ)^35 ≤ (22434868916561/100000000000000 : ℝ)^27 := by
    have hnat : (126282701 : ℕ)^35*100000000000000^27 ≤ 22434868916561^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126282701 400000000 22434868916561 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6180014883/10000000000 : ℝ), (830825909/2500000000 : ℝ), (126282701/400000000 : ℝ)] ![(53587129046987/100000000000000 : ℝ), (23978002017881/100000000000000 : ℝ), (22434868916561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6180014883/10000000000 : ℝ)|^35 ≤ (53587129046987/100000000000000 : ℝ)^27
        have hw : |(6180014883/10000000000 : ℝ)|=(6180014883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(830825909/2500000000 : ℝ)|^35 ≤ (23978002017881/100000000000000 : ℝ)^27
        have hw : |(830825909/2500000000 : ℝ)|=(830825909/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(126282701/400000000 : ℝ)|^35 ≤ (22434868916561/100000000000000 : ℝ)^27
        have hw : |(126282701/400000000 : ℝ)|=(126282701/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309086_s2_s2_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5838052353/10000000000 : ℝ)*x 0 + (-3547701083/10000000000 : ℝ)*x 1 + (-3339248157/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5838052353/10000000000 : ℝ)^35 ≤ (6221914916647/12500000000000 : ℝ)^27 := by
    have hnat : (5838052353 : ℕ)^35*12500000000000^27 ≤ 6221914916647^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5838052353 10000000000 6221914916647 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3547701083/10000000000 : ℝ)^35 ≤ (326218061461/1250000000000 : ℝ)^27 := by
    have hnat : (3547701083 : ℕ)^35*1250000000000^27 ≤ 326218061461^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3547701083 10000000000 326218061461 1250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3339248157/10000000000 : ℝ)^35 ≤ (4825447147253/20000000000000 : ℝ)^27 := by
    have hnat : (3339248157 : ℕ)^35*20000000000000^27 ≤ 4825447147253^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3339248157 10000000000 4825447147253 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5838052353/10000000000 : ℝ), (-3547701083/10000000000 : ℝ), (-3339248157/10000000000 : ℝ)] ![(6221914916647/12500000000000 : ℝ), (326218061461/1250000000000 : ℝ), (4825447147253/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5838052353/10000000000 : ℝ)|^35 ≤ (6221914916647/12500000000000 : ℝ)^27
        have hw : |(5838052353/10000000000 : ℝ)|=(5838052353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3547701083/10000000000 : ℝ)|^35 ≤ (326218061461/1250000000000 : ℝ)^27
        have hw : |(-3547701083/10000000000 : ℝ)|=(3547701083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3339248157/10000000000 : ℝ)|^35 ≤ (4825447147253/20000000000000 : ℝ)^27
        have hw : |(-3339248157/10000000000 : ℝ)|=(3339248157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309086_s2_s2_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-36218939/10000000000 : ℝ)*x 0 + (-7203644983/10000000000 : ℝ)*x 1 + (440661591/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (36218939/10000000000 : ℝ)^35 ≤ (34247385647/50000000000000 : ℝ)^27 := by
    have hnat : (36218939 : ℕ)^35*50000000000000^27 ≤ 34247385647^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36218939 10000000000 34247385647 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7203644983/10000000000 : ℝ)^35 ≤ (65365046704863/100000000000000 : ℝ)^27 := by
    have hnat : (7203644983 : ℕ)^35*100000000000000^27 ≤ 65365046704863^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7203644983 10000000000 65365046704863 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (440661591/1000000000 : ℝ)^35 ≤ (17283229258077/50000000000000 : ℝ)^27 := by
    have hnat : (440661591 : ℕ)^35*50000000000000^27 ≤ 17283229258077^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440661591 1000000000 17283229258077 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-36218939/10000000000 : ℝ), (-7203644983/10000000000 : ℝ), (440661591/1000000000 : ℝ)] ![(34247385647/50000000000000 : ℝ), (65365046704863/100000000000000 : ℝ), (17283229258077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-36218939/10000000000 : ℝ)|^35 ≤ (34247385647/50000000000000 : ℝ)^27
        have hw : |(-36218939/10000000000 : ℝ)|=(36218939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7203644983/10000000000 : ℝ)|^35 ≤ (65365046704863/100000000000000 : ℝ)^27
        have hw : |(-7203644983/10000000000 : ℝ)|=(7203644983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(440661591/1000000000 : ℝ)|^35 ≤ (17283229258077/50000000000000 : ℝ)^27
        have hw : |(440661591/1000000000 : ℝ)|=(440661591/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309086_s2_s2_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (48714069/80000000 : ℝ)*x 0 + (3319424649/10000000000 : ℝ)*x 1 + (3270901347/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (48714069/80000000 : ℝ)^35 ≤ (26284617401707/50000000000000 : ℝ)^27 := by
    have hnat : (48714069 : ℕ)^35*50000000000000^27 ≤ 26284617401707^27*80000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48714069 80000000 26284617401707 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3319424649/10000000000 : ℝ)^35 ≤ (23941728435483/100000000000000 : ℝ)^27 := by
    have hnat : (3319424649 : ℕ)^35*100000000000000^27 ≤ 23941728435483^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3319424649 10000000000 23941728435483 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3270901347/10000000000 : ℝ)^35 ≤ (4697807349441/20000000000000 : ℝ)^27 := by
    have hnat : (3270901347 : ℕ)^35*20000000000000^27 ≤ 4697807349441^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3270901347 10000000000 4697807349441 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(48714069/80000000 : ℝ), (3319424649/10000000000 : ℝ), (3270901347/10000000000 : ℝ)] ![(26284617401707/50000000000000 : ℝ), (23941728435483/100000000000000 : ℝ), (4697807349441/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(48714069/80000000 : ℝ)|^35 ≤ (26284617401707/50000000000000 : ℝ)^27
        have hw : |(48714069/80000000 : ℝ)|=(48714069/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3319424649/10000000000 : ℝ)|^35 ≤ (23941728435483/100000000000000 : ℝ)^27
        have hw : |(3319424649/10000000000 : ℝ)|=(3319424649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3270901347/10000000000 : ℝ)|^35 ≤ (4697807349441/20000000000000 : ℝ)^27
        have hw : |(3270901347/10000000000 : ℝ)|=(3270901347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309086_s2_s2_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (746776349/1250000000 : ℝ)*x 0 + (-426691329/1250000000 : ℝ)*x 1 + (-1656912817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (746776349/1250000000 : ℝ)^35 ≤ (51285346634449/100000000000000 : ℝ)^27 := by
    have hnat : (746776349 : ℕ)^35*100000000000000^27 ≤ 51285346634449^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      746776349 1250000000 51285346634449 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (426691329/1250000000 : ℝ)^35 ≤ (24825260852653/100000000000000 : ℝ)^27 := by
    have hnat : (426691329 : ℕ)^35*100000000000000^27 ≤ 24825260852653^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426691329 1250000000 24825260852653 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1656912817/5000000000 : ℝ)^35 ≤ (2388939249709/10000000000000 : ℝ)^27 := by
    have hnat : (1656912817 : ℕ)^35*10000000000000^27 ≤ 2388939249709^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1656912817 5000000000 2388939249709 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(746776349/1250000000 : ℝ), (-426691329/1250000000 : ℝ), (-1656912817/5000000000 : ℝ)] ![(51285346634449/100000000000000 : ℝ), (24825260852653/100000000000000 : ℝ), (2388939249709/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(746776349/1250000000 : ℝ)|^35 ≤ (51285346634449/100000000000000 : ℝ)^27
        have hw : |(746776349/1250000000 : ℝ)|=(746776349/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-426691329/1250000000 : ℝ)|^35 ≤ (24825260852653/100000000000000 : ℝ)^27
        have hw : |(-426691329/1250000000 : ℝ)|=(426691329/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1656912817/5000000000 : ℝ)|^35 ≤ (2388939249709/10000000000000 : ℝ)^27
        have hw : |(-1656912817/5000000000 : ℝ)|=(1656912817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309086_s2_s2_13 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2812871691/10000000000 : ℝ)*x 0 + (-1365982/9765625 : ℝ)*x 1 + (7833980259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2812871691/10000000000 : ℝ)^35 ≤ (9658397802087/50000000000000 : ℝ)^27 := by
    have hnat : (2812871691 : ℕ)^35*50000000000000^27 ≤ 9658397802087^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2812871691 10000000000 9658397802087 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1365982/9765625 : ℝ)^35 ≤ (976207935779/12500000000000 : ℝ)^27 := by
    have hnat : (1365982 : ℕ)^35*12500000000000^27 ≤ 976207935779^27*9765625^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365982 9765625 976207935779 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7833980259/10000000000 : ℝ)^35 ≤ (4554596305481/6250000000000 : ℝ)^27 := by
    have hnat : (7833980259 : ℕ)^35*6250000000000^27 ≤ 4554596305481^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7833980259 10000000000 4554596305481 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2812871691/10000000000 : ℝ), (-1365982/9765625 : ℝ), (7833980259/10000000000 : ℝ)] ![(9658397802087/50000000000000 : ℝ), (976207935779/12500000000000 : ℝ), (4554596305481/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2812871691/10000000000 : ℝ)|^35 ≤ (9658397802087/50000000000000 : ℝ)^27
        have hw : |(2812871691/10000000000 : ℝ)|=(2812871691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1365982/9765625 : ℝ)|^35 ≤ (976207935779/12500000000000 : ℝ)^27
        have hw : |(-1365982/9765625 : ℝ)|=(1365982/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7833980259/10000000000 : ℝ)|^35 ≤ (4554596305481/6250000000000 : ℝ)^27
        have hw : |(7833980259/10000000000 : ℝ)|=(7833980259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309086_s2_s2_14 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (969691/10000000000 : ℝ)*x 0 + (-1143145991/2000000000 : ℝ)*x 1 + (5999933621/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (969691/10000000000 : ℝ)^35 ≤ (313658961/50000000000000 : ℝ)^27 := by
    have hnat : (969691 : ℕ)^35*50000000000000^27 ≤ 313658961^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969691 10000000000 313658961 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1143145991/2000000000 : ℝ)^35 ≤ (48427600043407/100000000000000 : ℝ)^27 := by
    have hnat : (1143145991 : ℕ)^35*100000000000000^27 ≤ 48427600043407^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143145991 2000000000 48427600043407 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5999933621/10000000000 : ℝ)^35 ≤ (5157177262353/10000000000000 : ℝ)^27 := by
    have hnat : (5999933621 : ℕ)^35*10000000000000^27 ≤ 5157177262353^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5999933621 10000000000 5157177262353 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(969691/10000000000 : ℝ), (-1143145991/2000000000 : ℝ), (5999933621/10000000000 : ℝ)] ![(313658961/50000000000000 : ℝ), (48427600043407/100000000000000 : ℝ), (5157177262353/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(969691/10000000000 : ℝ)|^35 ≤ (313658961/50000000000000 : ℝ)^27
        have hw : |(969691/10000000000 : ℝ)|=(969691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1143145991/2000000000 : ℝ)|^35 ≤ (48427600043407/100000000000000 : ℝ)^27
        have hw : |(-1143145991/2000000000 : ℝ)|=(1143145991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5999933621/10000000000 : ℝ)|^35 ≤ (5157177262353/10000000000000 : ℝ)^27
        have hw : |(5999933621/10000000000 : ℝ)|=(5999933621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309086_s2_s2_15 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3419736273/5000000000 : ℝ)*x 0 + (748802799/2500000000 : ℝ)*x 1 + (21246797/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3419736273/5000000000 : ℝ)^35 ≤ (6111395937503/10000000000000 : ℝ)^27 := by
    have hnat : (3419736273 : ℕ)^35*10000000000000^27 ≤ 6111395937503^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3419736273 5000000000 6111395937503 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (748802799/2500000000 : ℝ)^35 ≤ (10477673172903/50000000000000 : ℝ)^27 := by
    have hnat : (748802799 : ℕ)^35*50000000000000^27 ≤ 10477673172903^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      748802799 2500000000 10477673172903 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21246797/80000000 : ℝ)^35 ≤ (2241336783989/12500000000000 : ℝ)^27 := by
    have hnat : (21246797 : ℕ)^35*12500000000000^27 ≤ 2241336783989^27*80000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21246797 80000000 2241336783989 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3419736273/5000000000 : ℝ), (748802799/2500000000 : ℝ), (21246797/80000000 : ℝ)] ![(6111395937503/10000000000000 : ℝ), (10477673172903/50000000000000 : ℝ), (2241336783989/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3419736273/5000000000 : ℝ)|^35 ≤ (6111395937503/10000000000000 : ℝ)^27
        have hw : |(3419736273/5000000000 : ℝ)|=(3419736273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(748802799/2500000000 : ℝ)|^35 ≤ (10477673172903/50000000000000 : ℝ)^27
        have hw : |(748802799/2500000000 : ℝ)|=(748802799/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21246797/80000000 : ℝ)|^35 ≤ (2241336783989/12500000000000 : ℝ)^27
        have hw : |(21246797/80000000 : ℝ)|=(21246797/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309086_s2_s2_16 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3230358927/5000000000 : ℝ)*x 0 + (-3350108621/10000000000 : ℝ)*x 1 + (-69452117/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3230358927/5000000000 : ℝ)^35 ≤ (56763304713/100000000000 : ℝ)^27 := by
    have hnat : (3230358927 : ℕ)^35*100000000000^27 ≤ 56763304713^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3230358927 5000000000 56763304713 100000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3350108621/10000000000 : ℝ)^35 ≤ (2422900592513/10000000000000 : ℝ)^27 := by
    have hnat : (3350108621 : ℕ)^35*10000000000000^27 ≤ 2422900592513^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3350108621 10000000000 2422900592513 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (69452117/250000000 : ℝ)^35 ≤ (950384467037/5000000000000 : ℝ)^27 := by
    have hnat : (69452117 : ℕ)^35*5000000000000^27 ≤ 950384467037^27*250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69452117 250000000 950384467037 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3230358927/5000000000 : ℝ), (-3350108621/10000000000 : ℝ), (-69452117/250000000 : ℝ)] ![(56763304713/100000000000 : ℝ), (2422900592513/10000000000000 : ℝ), (950384467037/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3230358927/5000000000 : ℝ)|^35 ≤ (56763304713/100000000000 : ℝ)^27
        have hw : |(3230358927/5000000000 : ℝ)|=(3230358927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3350108621/10000000000 : ℝ)|^35 ≤ (2422900592513/10000000000000 : ℝ)^27
        have hw : |(-3350108621/10000000000 : ℝ)|=(3350108621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-69452117/250000000 : ℝ)|^35 ≤ (950384467037/5000000000000 : ℝ)^27
        have hw : |(-69452117/250000000 : ℝ)|=(69452117/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309086_s2_s2_20 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1550606221/5000000000 : ℝ)*x 0 + (-2500215869/10000000000 : ℝ)*x 1 + (1718144453/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1550606221/5000000000 : ℝ)^35 ≤ (21921697954847/100000000000000 : ℝ)^27 := by
    have hnat : (1550606221 : ℕ)^35*100000000000000^27 ≤ 21921697954847^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1550606221 5000000000 21921697954847 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2500215869/10000000000 : ℝ)^35 ≤ (8290304394713/50000000000000 : ℝ)^27 := by
    have hnat : (2500215869 : ℕ)^35*50000000000000^27 ≤ 8290304394713^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2500215869 10000000000 8290304394713 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1718144453/2500000000 : ℝ)^35 ≤ (30748846622877/50000000000000 : ℝ)^27 := by
    have hnat : (1718144453 : ℕ)^35*50000000000000^27 ≤ 30748846622877^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1718144453 2500000000 30748846622877 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1550606221/5000000000 : ℝ), (-2500215869/10000000000 : ℝ), (1718144453/2500000000 : ℝ)] ![(21921697954847/100000000000000 : ℝ), (8290304394713/50000000000000 : ℝ), (30748846622877/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1550606221/5000000000 : ℝ)|^35 ≤ (21921697954847/100000000000000 : ℝ)^27
        have hw : |(1550606221/5000000000 : ℝ)|=(1550606221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2500215869/10000000000 : ℝ)|^35 ≤ (8290304394713/50000000000000 : ℝ)^27
        have hw : |(-2500215869/10000000000 : ℝ)|=(2500215869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1718144453/2500000000 : ℝ)|^35 ≤ (30748846622877/50000000000000 : ℝ)^27
        have hw : |(1718144453/2500000000 : ℝ)|=(1718144453/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309086_s2_s2_21 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (16731961/10000000000 : ℝ)*x 0 + (-3293638973/5000000000 : ℝ)*x 1 + (1019815309/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16731961/10000000000 : ℝ)^35 ≤ (2517062831/10000000000000 : ℝ)^27 := by
    have hnat : (16731961 : ℕ)^35*10000000000000^27 ≤ 2517062831^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16731961 10000000000 2517062831 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3293638973/5000000000 : ℝ)^35 ≤ (5820888018869/10000000000000 : ℝ)^27 := by
    have hnat : (3293638973 : ℕ)^35*10000000000000^27 ≤ 5820888018869^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3293638973 5000000000 5820888018869 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1019815309/2000000000 : ℝ)^35 ≤ (41765949167949/100000000000000 : ℝ)^27 := by
    have hnat : (1019815309 : ℕ)^35*100000000000000^27 ≤ 41765949167949^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019815309 2000000000 41765949167949 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16731961/10000000000 : ℝ), (-3293638973/5000000000 : ℝ), (1019815309/2000000000 : ℝ)] ![(2517062831/10000000000000 : ℝ), (5820888018869/10000000000000 : ℝ), (41765949167949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16731961/10000000000 : ℝ)|^35 ≤ (2517062831/10000000000000 : ℝ)^27
        have hw : |(16731961/10000000000 : ℝ)|=(16731961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3293638973/5000000000 : ℝ)|^35 ≤ (5820888018869/10000000000000 : ℝ)^27
        have hw : |(-3293638973/5000000000 : ℝ)|=(3293638973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1019815309/2000000000 : ℝ)|^35 ≤ (41765949167949/100000000000000 : ℝ)^27
        have hw : |(1019815309/2000000000 : ℝ)|=(1019815309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309086_s2_s2_22 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3368530761/5000000000 : ℝ)*x 0 + (187903299/625000000 : ℝ)*x 1 + (694650389/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3368530761/5000000000 : ℝ)^35 ≤ (59930370374111/100000000000000 : ℝ)^27 := by
    have hnat : (3368530761 : ℕ)^35*100000000000000^27 ≤ 59930370374111^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3368530761 5000000000 59930370374111 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (187903299/625000000 : ℝ)^35 ≤ (21057355826799/100000000000000 : ℝ)^27 := by
    have hnat : (187903299 : ℕ)^35*100000000000000^27 ≤ 21057355826799^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187903299 625000000 21057355826799 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (694650389/2500000000 : ℝ)^35 ≤ (9506136891267/50000000000000 : ℝ)^27 := by
    have hnat : (694650389 : ℕ)^35*50000000000000^27 ≤ 9506136891267^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      694650389 2500000000 9506136891267 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3368530761/5000000000 : ℝ), (187903299/625000000 : ℝ), (694650389/2500000000 : ℝ)] ![(59930370374111/100000000000000 : ℝ), (21057355826799/100000000000000 : ℝ), (9506136891267/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3368530761/5000000000 : ℝ)|^35 ≤ (59930370374111/100000000000000 : ℝ)^27
        have hw : |(3368530761/5000000000 : ℝ)|=(3368530761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(187903299/625000000 : ℝ)|^35 ≤ (21057355826799/100000000000000 : ℝ)^27
        have hw : |(187903299/625000000 : ℝ)|=(187903299/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(694650389/2500000000 : ℝ)|^35 ≤ (9506136891267/50000000000000 : ℝ)^27
        have hw : |(694650389/2500000000 : ℝ)|=(694650389/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309086_s2_s2_23 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (227877797/400000000 : ℝ)*x 0 + (-3726501487/10000000000 : ℝ)*x 1 + (-664352569/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (227877797/400000000 : ℝ)^35 ≤ (9644276486889/20000000000000 : ℝ)^27 := by
    have hnat : (227877797 : ℕ)^35*20000000000000^27 ≤ 9644276486889^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227877797 400000000 9644276486889 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3726501487/10000000000 : ℝ)^35 ≤ (556300508803/2000000000000 : ℝ)^27 := by
    have hnat : (3726501487 : ℕ)^35*2000000000000^27 ≤ 556300508803^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3726501487 10000000000 556300508803 2000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (664352569/2000000000 : ℝ)^35 ≤ (1497724506991/6250000000000 : ℝ)^27 := by
    have hnat : (664352569 : ℕ)^35*6250000000000^27 ≤ 1497724506991^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664352569 2000000000 1497724506991 6250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(227877797/400000000 : ℝ), (-3726501487/10000000000 : ℝ), (-664352569/2000000000 : ℝ)] ![(9644276486889/20000000000000 : ℝ), (556300508803/2000000000000 : ℝ), (1497724506991/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(227877797/400000000 : ℝ)|^35 ≤ (9644276486889/20000000000000 : ℝ)^27
        have hw : |(227877797/400000000 : ℝ)|=(227877797/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3726501487/10000000000 : ℝ)|^35 ≤ (556300508803/2000000000000 : ℝ)^27
        have hw : |(-3726501487/10000000000 : ℝ)|=(3726501487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-664352569/2000000000 : ℝ)|^35 ≤ (1497724506991/6250000000000 : ℝ)^27
        have hw : |(-664352569/2000000000 : ℝ)|=(664352569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c309086_s2_s2_27 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4718398207/10000000000 : ℝ)*x 0 + (-274549037/1000000000 : ℝ)*x 1 + (5262693759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4718398207/10000000000 : ℝ)^35 ≤ (37769491287729/100000000000000 : ℝ)^27 := by
    have hnat : (4718398207 : ℕ)^35*100000000000000^27 ≤ 37769491287729^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4718398207 10000000000 37769491287729 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274549037/1000000000 : ℝ)^35 ≤ (18719105312571/100000000000000 : ℝ)^27 := by
    have hnat : (274549037 : ℕ)^35*100000000000000^27 ≤ 18719105312571^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274549037 1000000000 18719105312571 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5262693759/10000000000 : ℝ)^35 ≤ (21755701694761/50000000000000 : ℝ)^27 := by
    have hnat : (5262693759 : ℕ)^35*50000000000000^27 ≤ 21755701694761^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5262693759 10000000000 21755701694761 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4718398207/10000000000 : ℝ), (-274549037/1000000000 : ℝ), (5262693759/10000000000 : ℝ)] ![(37769491287729/100000000000000 : ℝ), (18719105312571/100000000000000 : ℝ), (21755701694761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4718398207/10000000000 : ℝ)|^35 ≤ (37769491287729/100000000000000 : ℝ)^27
        have hw : |(4718398207/10000000000 : ℝ)|=(4718398207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-274549037/1000000000 : ℝ)|^35 ≤ (18719105312571/100000000000000 : ℝ)^27
        have hw : |(-274549037/1000000000 : ℝ)|=(274549037/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5262693759/10000000000 : ℝ)|^35 ≤ (21755701694761/50000000000000 : ℝ)^27
        have hw : |(5262693759/10000000000 : ℝ)|=(5262693759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c309086_s2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((63741/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(63741/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-15951/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-15951/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39463/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(39463/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((14069/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14069/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-30307/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-30307/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1309/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1309/2500 : ℝ)*X 1 2) := by
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
  have main1 : (77509/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (77509/100000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (77509/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (91323/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base17 : ((1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s2_pow0 : (63741/100000 : ℝ) ^ (69/16 : ℝ) ≤ (14340238955145778339/100000000000000000000 : ℝ) := by
    have hpowers : (63741/100000 : ℝ)^69 ≤ (14340238955145778339/100000000000000000000 : ℝ)^16 := by
      have hnat : (63741 : ℕ)^69*100000000000000000000^16 ≤ 14340238955145778339^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        63741 100000 14340238955145778339 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (63741/100000 : ℝ)) (X := (14340238955145778339/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (114340238955145778339/100000000000000000000 : ℝ) ≤ (5157811269888429/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (114340238955145778339/100000000000000000000 : ℝ)^16 ≤ (5157811269888429/5000000000000000 : ℝ)^69 := by
      have hnat : (114340238955145778339 : ℕ)^16*5000000000000000^69 ≤ 5157811269888429^69*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        114340238955145778339 100000000000000000000 5157811269888429 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5157811269888429/5000000000000000 : ℝ)) (X := (114340238955145778339/100000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (64340238955145778339/50000000000000000000 : ℝ) ≤ (5301078623223193/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (64340238955145778339/50000000000000000000 : ℝ)^16 ≤ (5301078623223193/5000000000000000 : ℝ)^69 := by
      have hnat : (64340238955145778339 : ℕ)^16*5000000000000000^69 ≤ 5301078623223193^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64340238955145778339 50000000000000000000 5301078623223193 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5301078623223193/5000000000000000 : ℝ)) (X := (64340238955145778339/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(157811269888429/3187050000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(35816838333691/796762500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (63741/100000 : ℝ)) (alpha := (157811269888429/3187050000000000 : ℝ)) (beta := (35816838333691/796762500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (63741/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(157811269888429/3187050000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(35816838333691/796762500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (15951/20000 : ℝ) ^ (69/16 : ℝ) ≤ (37699103903921412243/100000000000000000000 : ℝ) := by
    have hpowers : (15951/20000 : ℝ)^69 ≤ (37699103903921412243/100000000000000000000 : ℝ)^16 := by
      have hnat : (15951 : ℕ)^69*100000000000000000000^16 ≤ 37699103903921412243^16*20000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15951 20000 37699103903921412243 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15951/20000 : ℝ)) (X := (37699103903921412243/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (137699103903921412243/100000000000000000000 : ℝ) ≤ (10770005138389053/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (137699103903921412243/100000000000000000000 : ℝ)^16 ≤ (10770005138389053/10000000000000000 : ℝ)^69 := by
      have hnat : (137699103903921412243 : ℕ)^16*10000000000000000^69 ≤ 10770005138389053^69*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        137699103903921412243 100000000000000000000 10770005138389053 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10770005138389053/10000000000000000 : ℝ)) (X := (137699103903921412243/100000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (87699103903921412243/50000000000000000000 : ℝ) ≤ (2278324277903223/2000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (87699103903921412243/50000000000000000000 : ℝ)^16 ≤ (2278324277903223/2000000000000000 : ℝ)^69 := by
      have hnat : (87699103903921412243 : ℕ)^16*2000000000000000^69 ≤ 2278324277903223^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        87699103903921412243 50000000000000000000 2278324277903223 2000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2278324277903223/2000000000000000 : ℝ)) (X := (87699103903921412243/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(770005138389053/7975500000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(103602708521177/1329250000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (15951/20000 : ℝ)) (alpha := (770005138389053/7975500000000000 : ℝ)) (beta := (103602708521177/1329250000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (15951/20000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(770005138389053/7975500000000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(103602708521177/1329250000000000 : ℝ)*((1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (39463/50000 : ℝ) ^ (69/16 : ℝ) ≤ (36038080555295610451/100000000000000000000 : ℝ) := by
    have hpowers : (39463/50000 : ℝ)^69 ≤ (36038080555295610451/100000000000000000000 : ℝ)^16 := by
      have hnat : (39463 : ℕ)^69*100000000000000000000^16 ≤ 36038080555295610451^16*50000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39463 50000 36038080555295610451 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39463/50000 : ℝ)) (X := (36038080555295610451/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (136038080555295610451/100000000000000000000 : ℝ) ≤ (10739739270864331/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (136038080555295610451/100000000000000000000 : ℝ)^16 ≤ (10739739270864331/10000000000000000 : ℝ)^69 := by
      have hnat : (136038080555295610451 : ℕ)^16*10000000000000000^69 ≤ 10739739270864331^69*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        136038080555295610451 100000000000000000000 10739739270864331 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10739739270864331/10000000000000000 : ℝ)) (X := (136038080555295610451/100000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (86038080555295610451/50000000000000000000 : ℝ) ≤ (11341222595720281/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (86038080555295610451/50000000000000000000 : ℝ)^16 ≤ (11341222595720281/10000000000000000 : ℝ)^69 := by
      have hnat : (86038080555295610451 : ℕ)^16*10000000000000000^69 ≤ 11341222595720281^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        86038080555295610451 50000000000000000000 11341222595720281 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11341222595720281/10000000000000000 : ℝ)) (X := (86038080555295610451/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(739739270864331/7892600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(12029666497119/157852000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (69/16 : ℝ)) (rho := (39463/50000 : ℝ)) (alpha := (739739270864331/7892600000000000 : ℝ)) (beta := (12029666497119/157852000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (39463/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(739739270864331/7892600000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(12029666497119/157852000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_1 : ((6180014883/10000000000 : ℝ)*X 1 0+(830825909/2500000000 : ℝ)*X 1 1+(126282701/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309086_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((5838052353/10000000000 : ℝ)*X 2 0+(-3547701083/10000000000 : ℝ)*X 2 1+(-3339248157/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309086_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-36218939/10000000000 : ℝ)*X 0 0+(-7203644983/10000000000 : ℝ)*X 0 1+(440661591/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309086_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((48714069/80000000 : ℝ)*X 1 0+(3319424649/10000000000 : ℝ)*X 1 1+(3270901347/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309086_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((746776349/1250000000 : ℝ)*X 2 0+(-426691329/1250000000 : ℝ)*X 2 1+(-1656912817/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309086_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((2812871691/10000000000 : ℝ)*X 0 0+(-1365982/9765625 : ℝ)*X 0 1+(7833980259/10000000000 : ℝ)*X 0 2+(2812871691/10000000000 : ℝ)*X 1 0+(-1365982/9765625 : ℝ)*X 1 1+(7833980259/10000000000 : ℝ)*X 1 2+(2812871691/10000000000 : ℝ)*X 2 0+(-1365982/9765625 : ℝ)*X 2 1+(7833980259/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309086_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((969691/10000000000 : ℝ)*X 0 0+(-1143145991/2000000000 : ℝ)*X 0 1+(5999933621/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309086_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((3419736273/5000000000 : ℝ)*X 1 0+(748802799/2500000000 : ℝ)*X 1 1+(21246797/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309086_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((3230358927/5000000000 : ℝ)*X 2 0+(-3350108621/10000000000 : ℝ)*X 2 1+(-69452117/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309086_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((1550606221/5000000000 : ℝ)*X 0 0+(-2500215869/10000000000 : ℝ)*X 0 1+(1718144453/2500000000 : ℝ)*X 0 2+(1550606221/5000000000 : ℝ)*X 1 0+(-2500215869/10000000000 : ℝ)*X 1 1+(1718144453/2500000000 : ℝ)*X 1 2+(1550606221/5000000000 : ℝ)*X 2 0+(-2500215869/10000000000 : ℝ)*X 2 1+(1718144453/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309086_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((16731961/10000000000 : ℝ)*X 0 0+(-3293638973/5000000000 : ℝ)*X 0 1+(1019815309/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c309086_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((3368530761/5000000000 : ℝ)*X 1 0+(187903299/625000000 : ℝ)*X 1 1+(694650389/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c309086_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((227877797/400000000 : ℝ)*X 2 0+(-3726501487/10000000000 : ℝ)*X 2 1+(-664352569/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c309086_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((4718398207/10000000000 : ℝ)*X 0 0+(-274549037/1000000000 : ℝ)*X 0 1+(5262693759/10000000000 : ℝ)*X 0 2+(4718398207/10000000000 : ℝ)*X 1 0+(-274549037/1000000000 : ℝ)*X 1 1+(5262693759/10000000000 : ℝ)*X 1 2+(4718398207/10000000000 : ℝ)*X 2 0+(-274549037/1000000000 : ℝ)*X 2 1+(5262693759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c309086_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((14069/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14069/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3226817395933233199360975127487/445814690943700000000000000000000000 : ℝ) := by norm_num
    linear_combination (626753/500000000000 : ℝ)*(base17) + (214101/250000000000 : ℝ)*(base19) + (179674626789/500000000000 : ℝ)*(base40) + (24153/15625000000 : ℝ)*(base60) + (3447553568387/1000000000000 : ℝ)*(major_s2_0) + (3447553568387/1000000000000 : ℝ)*(major_s2_1) + (3447553568387/1000000000000 : ℝ)*(major_s2_2) + (178128563/1000000000000 : ℝ)*(sp_s2_2) + (4730121459801/1000000000000 : ℝ)*(sp_s2_7) + (2365096514099/500000000000 : ℝ)*(sp_s2_8) + (946003401909/200000000000 : ℝ)*(sp_s2_9) + (432973282687/200000000000 : ℝ)*(sp_s2_13) + (8634509/200000000000 : ℝ)*(sp_s2_20) + (18419577/250000000000 : ℝ)*(sp_s2_21) + (2164909585981/1000000000000 : ℝ)*(f.failure) + (4730195138109/1000000000000 : ℝ)*(f.sum) + (136707088363672018493/209824771000000000000000000000000 : ℝ)*base63 + (166900169122471/789260000000000000000000000 : ℝ)*base65 + (5424467391556261/7975500000000000000000000000 : ℝ)*base67 + (8127749099860597/7892600000000000000000000000 : ℝ)*base69 + (100722383632041259363/251541108300000000000000000000000 : ℝ)*base71 + (3919832780400413/3187050000000000000000000000 : ℝ)*base73 + (1162461418788549/1329250000000000000000000000 : ℝ)*base75 + (2171469241041907/3187050000000000000000000000 : ℝ)*base76 + (24771015201001045459/56485149500000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (1/1000000000000 : ℝ)*base84 + (16307/100000000000000000 : ℝ)*base87 + (16307/100000000000000000 : ℝ)*base89 + (16307/100000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-30307/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-30307/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2546471240162579739186506815639/222907345471850000000000000000000000 : ℝ) := by norm_num
    linear_combination (114013650751/500000000000 : ℝ)*(base7) + (12662993/500000000000 : ℝ)*(base21) + (1338156977129/1000000000000 : ℝ)*(base40) + (206607057983/1000000000000 : ℝ)*(base60) + (1463906664709/250000000000 : ℝ)*(major_s2_0) + (1463906664709/250000000000 : ℝ)*(major_s2_1) + (1463906664709/250000000000 : ℝ)*(major_s2_2) + (189639789/1000000000000 : ℝ)*(sp_s2_9) + (3947675023343/500000000000 : ℝ)*(sp_s2_14) + (3947552428323/500000000000 : ℝ)*(sp_s2_15) + (7895135080911/1000000000000 : ℝ)*(sp_s2_16) + (78101787099/20000000000 : ℝ)*(sp_s2_20) + (6129751/25000000000 : ℝ)*(sp_s2_22) + (9827867/1000000000000 : ℝ)*(sp_s2_27) + (1838535940657/500000000000 : ℝ)*(f.failure) + (3947675023343/500000000000 : ℝ)*(f.sum) + (12203128045016683687/26228096375000000000000000000000 : ℝ)*base62 + (252635480369/3946300000000000000000000 : ℝ)*base65 + (1670808887251571/3987750000000000000000000000 : ℝ)*base66 + (16570991996239/30830468750000000000000000 : ℝ)*base68 + (13852086675383236841/62885277075000000000000000000000 : ℝ)*base71 + (2140018615866611/3187050000000000000000000000 : ℝ)*base72 + (398178922444203/1329250000000000000000000000 : ℝ)*base74 + (1677511351517539/3187050000000000000000000000 : ℝ)*base77 + (15602184932058652199/28242574750000000000000000000000 : ℝ)*base78 + (5279/50000000000000000 : ℝ)*base87 + (5279/50000000000000000 : ℝ)*base89 + (5279/50000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1309/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1309/2500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17986447199996866250990775881983/2229073454718500000000000000000000000 : ℝ) := by norm_num
    linear_combination (19409/125000000000 : ℝ)*(base22) + (525485176919/250000000000 : ℝ)*(base40) + (1208591/500000000000 : ℝ)*(base50) + (91927/500000000000 : ℝ)*(base59) + (7878736456193/1000000000000 : ℝ)*(major_s2_0) + (7878736456193/1000000000000 : ℝ)*(major_s2_1) + (7878736456193/1000000000000 : ℝ)*(major_s2_2) + (25143741/250000000000 : ℝ)*(sp_s2_1) + (34073731/1000000000000 : ℝ)*(sp_s2_7) + (964569097/1000000000000 : ℝ)*(sp_s2_15) + (2702485429547/250000000000 : ℝ)*(sp_s2_21) + (5404455323929/500000000000 : ℝ)*(sp_s2_22) + (10809975636647/1000000000000 : ℝ)*(sp_s2_23) + (989498886157/200000000000 : ℝ)*(sp_s2_27) + (989498886157/200000000000 : ℝ)*(f.failure) + (10809975791919/1000000000000 : ℝ)*(f.sum) + (123415636718344538327/209824771000000000000000000000000 : ℝ)*base63 + (280325203757289/789260000000000000000000000 : ℝ)*base64 + (406619999393479/7975500000000000000000000000 : ℝ)*base67 + (2970023765885183/7892600000000000000000000000 : ℝ)*base69 + (61559319055712080193/251541108300000000000000000000000 : ℝ)*base70 + (45977482093591/99595312500000000000000000 : ℝ)*base73 + (1100129920461911/1329250000000000000000000000 : ℝ)*base75 + (102386595644651/398381250000000000000000000 : ℝ)*base76 + (6609165388952097199/56485149500000000000000000000000 : ℝ)*base78 + (16221/20000000000000000 : ℝ)*base86 + (16221/20000000000000000 : ℝ)*base88 + (16221/20000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (159247/100000 : ℝ) (91323/50000 : ℝ) (77509/100000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((63741/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(63741/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-15951/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-15951/20000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(39463/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(39463/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((14069/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14069/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-30307/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-30307/50000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(1309/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(1309/2500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c309086_s2 p hpa hpb X hX hprev1

#print axioms solution
