-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c328055_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:22:42.929287+00:00
-- url     : https://prove2.me/submissions/53ccf862-bbaa-45ad-94b1-60d9c0dbe6ce

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
theorem collision_support_c328055_s1_s1_1 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4705776179/10000000000 : ℝ)*x 0 + (-871220029/10000000000 : ℝ)*x 1 + (6051542739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4705776179/10000000000 : ℝ)^93 ≤ (40235239904173/100000000000000 : ℝ)^77 := by
    have hnat : (4705776179 : ℕ)^93*100000000000000^77 ≤ 40235239904173^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4705776179 10000000000 40235239904173 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (871220029/10000000000 : ℝ)^93 ≤ (1311700505761/25000000000000 : ℝ)^77 := by
    have hnat : (871220029 : ℕ)^93*25000000000000^77 ≤ 1311700505761^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871220029 10000000000 1311700505761 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6051542739/10000000000 : ℝ)^93 ≤ (27258979027553/50000000000000 : ℝ)^77 := by
    have hnat : (6051542739 : ℕ)^93*50000000000000^77 ≤ 27258979027553^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6051542739 10000000000 27258979027553 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4705776179/10000000000 : ℝ), (-871220029/10000000000 : ℝ), (6051542739/10000000000 : ℝ)] ![(40235239904173/100000000000000 : ℝ), (1311700505761/25000000000000 : ℝ), (27258979027553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4705776179/10000000000 : ℝ)|^93 ≤ (40235239904173/100000000000000 : ℝ)^77
        have hw : |(4705776179/10000000000 : ℝ)|=(4705776179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-871220029/10000000000 : ℝ)|^93 ≤ (1311700505761/25000000000000 : ℝ)^77
        have hw : |(-871220029/10000000000 : ℝ)|=(871220029/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6051542739/10000000000 : ℝ)|^93 ≤ (27258979027553/50000000000000 : ℝ)^77
        have hw : |(6051542739/10000000000 : ℝ)|=(6051542739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328055_s1_s1_2 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2349049979/5000000000 : ℝ)*x 0 + (5496223671/10000000000 : ℝ)*x 1 + (-1645462503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2349049979/5000000000 : ℝ)^93 ≤ (8031196443963/20000000000000 : ℝ)^77 := by
    have hnat : (2349049979 : ℕ)^93*20000000000000^77 ≤ 8031196443963^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2349049979 5000000000 8031196443963 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5496223671/10000000000 : ℝ)^93 ≤ (48534639214477/100000000000000 : ℝ)^77 := by
    have hnat : (5496223671 : ℕ)^93*100000000000000^77 ≤ 48534639214477^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5496223671 10000000000 48534639214477 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1645462503/10000000000 : ℝ)^93 ≤ (11309378551069/100000000000000 : ℝ)^77 := by
    have hnat : (1645462503 : ℕ)^93*100000000000000^77 ≤ 11309378551069^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1645462503 10000000000 11309378551069 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2349049979/5000000000 : ℝ), (5496223671/10000000000 : ℝ), (-1645462503/10000000000 : ℝ)] ![(8031196443963/20000000000000 : ℝ), (48534639214477/100000000000000 : ℝ), (11309378551069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2349049979/5000000000 : ℝ)|^93 ≤ (8031196443963/20000000000000 : ℝ)^77
        have hw : |(2349049979/5000000000 : ℝ)|=(2349049979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5496223671/10000000000 : ℝ)|^93 ≤ (48534639214477/100000000000000 : ℝ)^77
        have hw : |(5496223671/10000000000 : ℝ)|=(5496223671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1645462503/10000000000 : ℝ)|^93 ≤ (11309378551069/100000000000000 : ℝ)^77
        have hw : |(-1645462503/10000000000 : ℝ)|=(1645462503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328055_s1_s1_7 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-88272407/625000000 : ℝ)*x 0 + (5009123373/10000000000 : ℝ)*x 1 + (537150027/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (88272407/625000000 : ℝ)^93 ≤ (9403946212857/100000000000000 : ℝ)^77 := by
    have hnat : (88272407 : ℕ)^93*100000000000000^77 ≤ 9403946212857^77*625000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88272407 625000000 9403946212857 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5009123373/10000000000 : ℝ)^93 ≤ (43388491885973/100000000000000 : ℝ)^77 := by
    have hnat : (5009123373 : ℕ)^93*100000000000000^77 ≤ 43388491885973^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5009123373 10000000000 43388491885973 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (537150027/1000000000 : ℝ)^93 ≤ (5900945235507/12500000000000 : ℝ)^77 := by
    have hnat : (537150027 : ℕ)^93*12500000000000^77 ≤ 5900945235507^77*1000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537150027 1000000000 5900945235507 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-88272407/625000000 : ℝ), (5009123373/10000000000 : ℝ), (537150027/1000000000 : ℝ)] ![(9403946212857/100000000000000 : ℝ), (43388491885973/100000000000000 : ℝ), (5900945235507/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-88272407/625000000 : ℝ)|^93 ≤ (9403946212857/100000000000000 : ℝ)^77
        have hw : |(-88272407/625000000 : ℝ)|=(88272407/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5009123373/10000000000 : ℝ)|^93 ≤ (43388491885973/100000000000000 : ℝ)^77
        have hw : |(5009123373/10000000000 : ℝ)|=(5009123373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(537150027/1000000000 : ℝ)|^93 ≤ (5900945235507/12500000000000 : ℝ)^77
        have hw : |(537150027/1000000000 : ℝ)|=(537150027/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328055_s1_s1_8 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (234715419/500000000 : ℝ)*x 0 + (-206227149/5000000000 : ℝ)*x 1 + (6347706769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (234715419/500000000 : ℝ)^93 ≤ (40116843754319/100000000000000 : ℝ)^77 := by
    have hnat : (234715419 : ℕ)^93*100000000000000^77 ≤ 40116843754319^77*500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234715419 500000000 40116843754319 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (206227149/5000000000 : ℝ)^93 ≤ (2126482049657/100000000000000 : ℝ)^77 := by
    have hnat : (206227149 : ℕ)^93*100000000000000^77 ≤ 2126482049657^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206227149 5000000000 2126482049657 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6347706769/10000000000 : ℝ)^93 ≤ (57756674185593/100000000000000 : ℝ)^77 := by
    have hnat : (6347706769 : ℕ)^93*100000000000000^77 ≤ 57756674185593^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6347706769 10000000000 57756674185593 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(234715419/500000000 : ℝ), (-206227149/5000000000 : ℝ), (6347706769/10000000000 : ℝ)] ![(40116843754319/100000000000000 : ℝ), (2126482049657/100000000000000 : ℝ), (57756674185593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(234715419/500000000 : ℝ)|^93 ≤ (40116843754319/100000000000000 : ℝ)^77
        have hw : |(234715419/500000000 : ℝ)|=(234715419/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-206227149/5000000000 : ℝ)|^93 ≤ (2126482049657/100000000000000 : ℝ)^77
        have hw : |(-206227149/5000000000 : ℝ)|=(206227149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6347706769/10000000000 : ℝ)|^93 ≤ (57756674185593/100000000000000 : ℝ)^77
        have hw : |(6347706769/10000000000 : ℝ)|=(6347706769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328055_s1_s1_9 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4686603277/10000000000 : ℝ)*x 0 + (2989608489/5000000000 : ℝ)*x 1 + (-200890129/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4686603277/10000000000 : ℝ)^93 ≤ (40037328269103/100000000000000 : ℝ)^77 := by
    have hnat : (4686603277 : ℕ)^93*100000000000000^77 ≤ 40037328269103^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4686603277 10000000000 40037328269103 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2989608489/5000000000 : ℝ)^93 ≤ (53731967390217/100000000000000 : ℝ)^77 := by
    have hnat : (2989608489 : ℕ)^93*100000000000000^77 ≤ 53731967390217^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2989608489 5000000000 53731967390217 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (200890129/2000000000 : ℝ)^93 ≤ (6230704326969/100000000000000 : ℝ)^77 := by
    have hnat : (200890129 : ℕ)^93*100000000000000^77 ≤ 6230704326969^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200890129 2000000000 6230704326969 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4686603277/10000000000 : ℝ), (2989608489/5000000000 : ℝ), (-200890129/2000000000 : ℝ)] ![(40037328269103/100000000000000 : ℝ), (53731967390217/100000000000000 : ℝ), (6230704326969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4686603277/10000000000 : ℝ)|^93 ≤ (40037328269103/100000000000000 : ℝ)^77
        have hw : |(4686603277/10000000000 : ℝ)|=(4686603277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2989608489/5000000000 : ℝ)|^93 ≤ (53731967390217/100000000000000 : ℝ)^77
        have hw : |(2989608489/5000000000 : ℝ)|=(2989608489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-200890129/2000000000 : ℝ)|^93 ≤ (6230704326969/100000000000000 : ℝ)^77
        have hw : |(-200890129/2000000000 : ℝ)|=(200890129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328055_s1_s1_13 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5429899793/10000000000 : ℝ)*x 0 + (5322052677/10000000000 : ℝ)*x 1 + (226085059/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5429899793/10000000000 : ℝ)^93 ≤ (47828154182107/100000000000000 : ℝ)^77 := by
    have hnat : (5429899793 : ℕ)^93*100000000000000^77 ≤ 47828154182107^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429899793 10000000000 47828154182107 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5322052677/10000000000 : ℝ)^93 ≤ (1458849786759/3125000000000 : ℝ)^77 := by
    have hnat : (5322052677 : ℕ)^93*3125000000000^77 ≤ 1458849786759^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5322052677 10000000000 1458849786759 3125000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226085059/2500000000 : ℝ)^93 ≤ (1372163157443/25000000000000 : ℝ)^77 := by
    have hnat : (226085059 : ℕ)^93*25000000000000^77 ≤ 1372163157443^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226085059 2500000000 1372163157443 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5429899793/10000000000 : ℝ), (5322052677/10000000000 : ℝ), (226085059/2500000000 : ℝ)] ![(47828154182107/100000000000000 : ℝ), (1458849786759/3125000000000 : ℝ), (1372163157443/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5429899793/10000000000 : ℝ)|^93 ≤ (47828154182107/100000000000000 : ℝ)^77
        have hw : |(5429899793/10000000000 : ℝ)|=(5429899793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5322052677/10000000000 : ℝ)|^93 ≤ (1458849786759/3125000000000 : ℝ)^77
        have hw : |(5322052677/10000000000 : ℝ)|=(5322052677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(226085059/2500000000 : ℝ)|^93 ≤ (1372163157443/25000000000000 : ℝ)^77
        have hw : |(226085059/2500000000 : ℝ)|=(226085059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328055_s1_s1_14 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-467064703/5000000000 : ℝ)*x 0 + (1053925123/2000000000 : ℝ)*x 1 + (1365360179/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (467064703/5000000000 : ℝ)^93 ≤ (713469912243/12500000000000 : ℝ)^77 := by
    have hnat : (467064703 : ℕ)^93*12500000000000^77 ≤ 713469912243^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467064703 5000000000 713469912243 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053925123/2000000000 : ℝ)^93 ≤ (9225666677641/20000000000000 : ℝ)^77 := by
    have hnat : (1053925123 : ℕ)^93*20000000000000^77 ≤ 9225666677641^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053925123 2000000000 9225666677641 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1365360179/2500000000 : ℝ)^93 ≤ (12040976823569/25000000000000 : ℝ)^77 := by
    have hnat : (1365360179 : ℕ)^93*25000000000000^77 ≤ 12040976823569^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1365360179 2500000000 12040976823569 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-467064703/5000000000 : ℝ), (1053925123/2000000000 : ℝ), (1365360179/2500000000 : ℝ)] ![(713469912243/12500000000000 : ℝ), (9225666677641/20000000000000 : ℝ), (12040976823569/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-467064703/5000000000 : ℝ)|^93 ≤ (713469912243/12500000000000 : ℝ)^77
        have hw : |(-467064703/5000000000 : ℝ)|=(467064703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053925123/2000000000 : ℝ)|^93 ≤ (9225666677641/20000000000000 : ℝ)^77
        have hw : |(1053925123/2000000000 : ℝ)|=(1053925123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1365360179/2500000000 : ℝ)|^93 ≤ (12040976823569/25000000000000 : ℝ)^77
        have hw : |(1365360179/2500000000 : ℝ)|=(1365360179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328055_s1_s1_15 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2225013651/5000000000 : ℝ)*x 0 + (-785301977/10000000000 : ℝ)*x 1 + (6348216299/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2225013651/5000000000 : ℝ)^93 ≤ (9402323468553/25000000000000 : ℝ)^77 := by
    have hnat : (2225013651 : ℕ)^93*25000000000000^77 ≤ 9402323468553^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2225013651 5000000000 9402323468553 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (785301977/10000000000 : ℝ)^93 ≤ (4628432401753/100000000000000 : ℝ)^77 := by
    have hnat : (785301977 : ℕ)^93*100000000000000^77 ≤ 4628432401753^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      785301977 10000000000 4628432401753 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6348216299/10000000000 : ℝ)^93 ≤ (57762273707207/100000000000000 : ℝ)^77 := by
    have hnat : (6348216299 : ℕ)^93*100000000000000^77 ≤ 57762273707207^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6348216299 10000000000 57762273707207 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2225013651/5000000000 : ℝ), (-785301977/10000000000 : ℝ), (6348216299/10000000000 : ℝ)] ![(9402323468553/25000000000000 : ℝ), (4628432401753/100000000000000 : ℝ), (57762273707207/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2225013651/5000000000 : ℝ)|^93 ≤ (9402323468553/25000000000000 : ℝ)^77
        have hw : |(2225013651/5000000000 : ℝ)|=(2225013651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-785301977/10000000000 : ℝ)|^93 ≤ (4628432401753/100000000000000 : ℝ)^77
        have hw : |(-785301977/10000000000 : ℝ)|=(785301977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6348216299/10000000000 : ℝ)|^93 ≤ (57762273707207/100000000000000 : ℝ)^77
        have hw : |(6348216299/10000000000 : ℝ)|=(6348216299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328055_s1_s1_16 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5452443437/10000000000 : ℝ)*x 0 + (5292339849/10000000000 : ℝ)*x 1 + (-457257301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5452443437/10000000000 : ℝ)^93 ≤ (48068090083031/100000000000000 : ℝ)^77 := by
    have hnat : (5452443437 : ℕ)^93*100000000000000^77 ≤ 48068090083031^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5452443437 10000000000 48068090083031 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5292339849/10000000000 : ℝ)^93 ≤ (9273717690293/20000000000000 : ℝ)^77 := by
    have hnat : (5292339849 : ℕ)^93*20000000000000^77 ≤ 9273717690293^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5292339849 10000000000 9273717690293 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (457257301/5000000000 : ℝ)^93 ≤ (1390830363807/25000000000000 : ℝ)^77 := by
    have hnat : (457257301 : ℕ)^93*25000000000000^77 ≤ 1390830363807^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457257301 5000000000 1390830363807 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5452443437/10000000000 : ℝ), (5292339849/10000000000 : ℝ), (-457257301/5000000000 : ℝ)] ![(48068090083031/100000000000000 : ℝ), (9273717690293/20000000000000 : ℝ), (1390830363807/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5452443437/10000000000 : ℝ)|^93 ≤ (48068090083031/100000000000000 : ℝ)^77
        have hw : |(5452443437/10000000000 : ℝ)|=(5452443437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5292339849/10000000000 : ℝ)|^93 ≤ (9273717690293/20000000000000 : ℝ)^77
        have hw : |(5292339849/10000000000 : ℝ)|=(5292339849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-457257301/5000000000 : ℝ)|^93 ≤ (1390830363807/25000000000000 : ℝ)^77
        have hw : |(-457257301/5000000000 : ℝ)|=(457257301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328055_s1_s1_20 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3603085731/5000000000 : ℝ)*x 0 + (850851477/2500000000 : ℝ)*x 1 + (902630831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3603085731/5000000000 : ℝ)^93 ≤ (6731885402071/10000000000000 : ℝ)^77 := by
    have hnat : (3603085731 : ℕ)^93*10000000000000^77 ≤ 6731885402071^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3603085731 5000000000 6731885402071 10000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (850851477/2500000000 : ℝ)^93 ≤ (27205021456221/100000000000000 : ℝ)^77 := by
    have hnat : (850851477 : ℕ)^93*100000000000000^77 ≤ 27205021456221^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      850851477 2500000000 27205021456221 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (902630831/10000000000 : ℝ)^93 ≤ (1095224902879/20000000000000 : ℝ)^77 := by
    have hnat : (902630831 : ℕ)^93*20000000000000^77 ≤ 1095224902879^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902630831 10000000000 1095224902879 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3603085731/5000000000 : ℝ), (850851477/2500000000 : ℝ), (902630831/10000000000 : ℝ)] ![(6731885402071/10000000000000 : ℝ), (27205021456221/100000000000000 : ℝ), (1095224902879/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3603085731/5000000000 : ℝ)|^93 ≤ (6731885402071/10000000000000 : ℝ)^77
        have hw : |(3603085731/5000000000 : ℝ)|=(3603085731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(850851477/2500000000 : ℝ)|^93 ≤ (27205021456221/100000000000000 : ℝ)^77
        have hw : |(850851477/2500000000 : ℝ)|=(850851477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(902630831/10000000000 : ℝ)|^93 ≤ (1095224902879/20000000000000 : ℝ)^77
        have hw : |(902630831/10000000000 : ℝ)|=(902630831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328055_s1_s1_21 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1027727499/10000000000 : ℝ)*x 0 + (5956957439/10000000000 : ℝ)*x 1 + (4693066503/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1027727499/10000000000 : ℝ)^93 ≤ (6405513051819/100000000000000 : ℝ)^77 := by
    have hnat : (1027727499 : ℕ)^93*100000000000000^77 ≤ 6405513051819^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027727499 10000000000 6405513051819 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5956957439/10000000000 : ℝ)^93 ≤ (13372615248023/25000000000000 : ℝ)^77 := by
    have hnat : (5956957439 : ℕ)^93*25000000000000^77 ≤ 13372615248023^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5956957439 10000000000 13372615248023 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4693066503/10000000000 : ℝ)^93 ≤ (40104025938987/100000000000000 : ℝ)^77 := by
    have hnat : (4693066503 : ℕ)^93*100000000000000^77 ≤ 40104025938987^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4693066503 10000000000 40104025938987 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1027727499/10000000000 : ℝ), (5956957439/10000000000 : ℝ), (4693066503/10000000000 : ℝ)] ![(6405513051819/100000000000000 : ℝ), (13372615248023/25000000000000 : ℝ), (40104025938987/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1027727499/10000000000 : ℝ)|^93 ≤ (6405513051819/100000000000000 : ℝ)^77
        have hw : |(-1027727499/10000000000 : ℝ)|=(1027727499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5956957439/10000000000 : ℝ)|^93 ≤ (13372615248023/25000000000000 : ℝ)^77
        have hw : |(5956957439/10000000000 : ℝ)|=(5956957439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4693066503/10000000000 : ℝ)|^93 ≤ (40104025938987/100000000000000 : ℝ)^77
        have hw : |(4693066503/10000000000 : ℝ)|=(4693066503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328055_s1_s1_22 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5366552023/10000000000 : ℝ)*x 0 + (-186869341/5000000000 : ℝ)*x 1 + (715300319/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5366552023/10000000000 : ℝ)^93 ≤ (47155042698283/100000000000000 : ℝ)^77 := by
    have hnat : (5366552023 : ℕ)^93*100000000000000^77 ≤ 47155042698283^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5366552023 10000000000 47155042698283 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (186869341/5000000000 : ℝ)^93 ≤ (471953077049/25000000000000 : ℝ)^77 := by
    have hnat : (186869341 : ℕ)^93*25000000000000^77 ≤ 471953077049^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186869341 5000000000 471953077049 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (715300319/1250000000 : ℝ)^93 ≤ (3184821561309/6250000000000 : ℝ)^77 := by
    have hnat : (715300319 : ℕ)^93*6250000000000^77 ≤ 3184821561309^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      715300319 1250000000 3184821561309 6250000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5366552023/10000000000 : ℝ), (-186869341/5000000000 : ℝ), (715300319/1250000000 : ℝ)] ![(47155042698283/100000000000000 : ℝ), (471953077049/25000000000000 : ℝ), (3184821561309/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5366552023/10000000000 : ℝ)|^93 ≤ (47155042698283/100000000000000 : ℝ)^77
        have hw : |(5366552023/10000000000 : ℝ)|=(5366552023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-186869341/5000000000 : ℝ)|^93 ≤ (471953077049/25000000000000 : ℝ)^77
        have hw : |(-186869341/5000000000 : ℝ)|=(186869341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(715300319/1250000000 : ℝ)|^93 ≤ (3184821561309/6250000000000 : ℝ)^77
        have hw : |(715300319/1250000000 : ℝ)|=(715300319/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328055_s1_s1_23 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (433461723/1000000000 : ℝ)*x 0 + (6017931983/10000000000 : ℝ)*x 1 + (-22085923/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433461723/1000000000 : ℝ)^93 ≤ (36434427383783/100000000000000 : ℝ)^77 := by
    have hnat : (433461723 : ℕ)^93*100000000000000^77 ≤ 36434427383783^77*1000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433461723 1000000000 36434427383783 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6017931983/10000000000 : ℝ)^93 ≤ (1692264168257/3125000000000 : ℝ)^77 := by
    have hnat : (6017931983 : ℕ)^93*3125000000000^77 ≤ 1692264168257^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6017931983 10000000000 1692264168257 3125000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22085923/156250000 : ℝ)^93 ≤ (941311922511/10000000000000 : ℝ)^77 := by
    have hnat : (22085923 : ℕ)^93*10000000000000^77 ≤ 941311922511^77*156250000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22085923 156250000 941311922511 10000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(433461723/1000000000 : ℝ), (6017931983/10000000000 : ℝ), (-22085923/156250000 : ℝ)] ![(36434427383783/100000000000000 : ℝ), (1692264168257/3125000000000 : ℝ), (941311922511/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(433461723/1000000000 : ℝ)|^93 ≤ (36434427383783/100000000000000 : ℝ)^77
        have hw : |(433461723/1000000000 : ℝ)|=(433461723/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6017931983/10000000000 : ℝ)|^93 ≤ (1692264168257/3125000000000 : ℝ)^77
        have hw : |(6017931983/10000000000 : ℝ)|=(6017931983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-22085923/156250000 : ℝ)|^93 ≤ (941311922511/10000000000000 : ℝ)^77
        have hw : |(-22085923/156250000 : ℝ)|=(22085923/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328055_s1_s1_27 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7565849113/10000000000 : ℝ)*x 0 + (1078376629/5000000000 : ℝ)*x 1 + (36747641/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7565849113/10000000000 : ℝ)^93 ≤ (71397868208187/100000000000000 : ℝ)^77 := by
    have hnat : (7565849113 : ℕ)^93*100000000000000^77 ≤ 71397868208187^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7565849113 10000000000 71397868208187 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078376629/5000000000 : ℝ)^93 ≤ (784042120203/5000000000000 : ℝ)^77 := by
    have hnat : (1078376629 : ℕ)^93*5000000000000^77 ≤ 784042120203^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078376629 5000000000 784042120203 5000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (36747641/200000000 : ℝ)^93 ≤ (12921289369457/100000000000000 : ℝ)^77 := by
    have hnat : (36747641 : ℕ)^93*100000000000000^77 ≤ 12921289369457^77*200000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36747641 200000000 12921289369457 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7565849113/10000000000 : ℝ), (1078376629/5000000000 : ℝ), (36747641/200000000 : ℝ)] ![(71397868208187/100000000000000 : ℝ), (784042120203/5000000000000 : ℝ), (12921289369457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7565849113/10000000000 : ℝ)|^93 ≤ (71397868208187/100000000000000 : ℝ)^77
        have hw : |(7565849113/10000000000 : ℝ)|=(7565849113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078376629/5000000000 : ℝ)|^93 ≤ (784042120203/5000000000000 : ℝ)^77
        have hw : |(1078376629/5000000000 : ℝ)|=(1078376629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(36747641/200000000 : ℝ)|^93 ≤ (12921289369457/100000000000000 : ℝ)^77
        have hw : |(36747641/200000000 : ℝ)|=(36747641/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c328055_s1 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((7889/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7889/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(60131/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(60131/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61091/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61091/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((759/2500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(759/2500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31089/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31089/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15019/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15019/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (82433/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (82433/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (82433/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (82433/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (82433/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (82433/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (7889/12500 : ℝ) ^ (91/16 : ℝ) ≤ (3648435563840698981/50000000000000000000 : ℝ) := by
    have hpowers : (7889/12500 : ℝ)^91 ≤ (3648435563840698981/50000000000000000000 : ℝ)^16 := by
      have hnat : (7889 : ℕ)^91*50000000000000000000^16 ≤ 3648435563840698981^16*12500^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7889 12500 3648435563840698981 50000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7889/12500 : ℝ)) (X := (3648435563840698981/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (53648435563840698981/50000000000000000000 : ℝ) ≤ (10124601631485469/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (53648435563840698981/50000000000000000000 : ℝ)^16 ≤ (10124601631485469/10000000000000000 : ℝ)^91 := by
      have hnat : (53648435563840698981 : ℕ)^16*10000000000000000^91 ≤ 10124601631485469^91*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53648435563840698981 50000000000000000000 10124601631485469 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10124601631485469/10000000000000000 : ℝ)) (X := (53648435563840698981/50000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (28648435563840698981/25000000000000000000 : ℝ) ≤ (5121202174485891/5000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (28648435563840698981/25000000000000000000 : ℝ)^16 ≤ (5121202174485891/5000000000000000 : ℝ)^91 := by
      have hnat : (28648435563840698981 : ℕ)^16*5000000000000000^91 ≤ 5121202174485891^91*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28648435563840698981 25000000000000000000 5121202174485891 5000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5121202174485891/5000000000000000 : ℝ)) (X := (28648435563840698981/25000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(124601631485469/6311200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(117802717486313/6311200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (7889/12500 : ℝ)) (alpha := (124601631485469/6311200000000000 : ℝ)) (beta := (117802717486313/6311200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (7889/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(124601631485469/6311200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(117802717486313/6311200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (60131/100000 : ℝ) ^ (91/16 : ℝ) ≤ (5541435722407261183/100000000000000000000 : ℝ) := by
    have hpowers : (60131/100000 : ℝ)^91 ≤ (5541435722407261183/100000000000000000000 : ℝ)^16 := by
      have hnat : (60131 : ℕ)^91*100000000000000000000^16 ≤ 5541435722407261183^16*100000^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60131 100000 5541435722407261183 100000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (60131/100000 : ℝ)) (X := (5541435722407261183/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (105541435722407261183/100000000000000000000 : ℝ) ≤ (10095279078421779/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (105541435722407261183/100000000000000000000 : ℝ)^16 ≤ (10095279078421779/10000000000000000 : ℝ)^91 := by
      have hnat : (105541435722407261183 : ℕ)^16*10000000000000000^91 ≤ 10095279078421779^91*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        105541435722407261183 100000000000000000000 10095279078421779 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10095279078421779/10000000000000000 : ℝ)) (X := (105541435722407261183/100000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (55541435722407261183/50000000000000000000 : ℝ) ≤ (5093260247425543/5000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (55541435722407261183/50000000000000000000 : ℝ)^16 ≤ (5093260247425543/5000000000000000 : ℝ)^91 := by
      have hnat : (55541435722407261183 : ℕ)^16*5000000000000000^91 ≤ 5093260247425543^91*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55541435722407261183 50000000000000000000 5093260247425543 5000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5093260247425543/5000000000000000 : ℝ)) (X := (55541435722407261183/50000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(95279078421779/6013100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(91241416429307/6013100000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (60131/100000 : ℝ)) (alpha := (95279078421779/6013100000000000 : ℝ)) (beta := (91241416429307/6013100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (60131/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(95279078421779/6013100000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(91241416429307/6013100000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (61091/100000 : ℝ) ^ (91/16 : ℝ) ≤ (3031904542199050723/50000000000000000000 : ℝ) := by
    have hpowers : (61091/100000 : ℝ)^91 ≤ (3031904542199050723/50000000000000000000 : ℝ)^16 := by
      have hnat : (61091 : ℕ)^91*50000000000000000000^16 ≤ 3031904542199050723^16*100000^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        61091 100000 3031904542199050723 50000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (61091/100000 : ℝ)) (X := (3031904542199050723/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (53031904542199050723/50000000000000000000 : ℝ) ≤ (10104046480190327/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (53031904542199050723/50000000000000000000 : ℝ)^16 ≤ (10104046480190327/10000000000000000 : ℝ)^91 := by
      have hnat : (53031904542199050723 : ℕ)^16*10000000000000000^91 ≤ 10104046480190327^91*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53031904542199050723 50000000000000000000 10104046480190327 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10104046480190327/10000000000000000 : ℝ)) (X := (53031904542199050723/50000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (28031904542199050723/25000000000000000000 : ℝ) ≤ (10203300476990479/10000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (28031904542199050723/25000000000000000000 : ℝ)^16 ≤ (10203300476990479/10000000000000000 : ℝ)^91 := by
      have hnat : (28031904542199050723 : ℕ)^16*10000000000000000^91 ≤ 10203300476990479^91*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28031904542199050723 25000000000000000000 10203300476990479 10000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10203300476990479/10000000000000000 : ℝ)) (X := (28031904542199050723/25000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(104046480190327/6109100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(12406749600019/763637500000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (61091/100000 : ℝ)) (alpha := (104046480190327/6109100000000000 : ℝ)) (beta := (12406749600019/763637500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (61091/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(104046480190327/6109100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(12406749600019/763637500000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_1 : ((4705776179/10000000000 : ℝ)*X 1 0+(-871220029/10000000000 : ℝ)*X 1 1+(6051542739/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328055_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2349049979/5000000000 : ℝ)*X 2 0+(5496223671/10000000000 : ℝ)*X 2 1+(-1645462503/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328055_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-88272407/625000000 : ℝ)*X 0 0+(5009123373/10000000000 : ℝ)*X 0 1+(537150027/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328055_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((234715419/500000000 : ℝ)*X 1 0+(-206227149/5000000000 : ℝ)*X 1 1+(6347706769/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328055_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4686603277/10000000000 : ℝ)*X 2 0+(2989608489/5000000000 : ℝ)*X 2 1+(-200890129/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328055_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((5429899793/10000000000 : ℝ)*X 0 0+(5322052677/10000000000 : ℝ)*X 0 1+(226085059/2500000000 : ℝ)*X 0 2+(5429899793/10000000000 : ℝ)*X 1 0+(5322052677/10000000000 : ℝ)*X 1 1+(226085059/2500000000 : ℝ)*X 1 2+(5429899793/10000000000 : ℝ)*X 2 0+(5322052677/10000000000 : ℝ)*X 2 1+(226085059/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328055_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-467064703/5000000000 : ℝ)*X 0 0+(1053925123/2000000000 : ℝ)*X 0 1+(1365360179/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328055_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2225013651/5000000000 : ℝ)*X 1 0+(-785301977/10000000000 : ℝ)*X 1 1+(6348216299/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328055_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((5452443437/10000000000 : ℝ)*X 2 0+(5292339849/10000000000 : ℝ)*X 2 1+(-457257301/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328055_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((3603085731/5000000000 : ℝ)*X 0 0+(850851477/2500000000 : ℝ)*X 0 1+(902630831/10000000000 : ℝ)*X 0 2+(3603085731/5000000000 : ℝ)*X 1 0+(850851477/2500000000 : ℝ)*X 1 1+(902630831/10000000000 : ℝ)*X 1 2+(3603085731/5000000000 : ℝ)*X 2 0+(850851477/2500000000 : ℝ)*X 2 1+(902630831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328055_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-1027727499/10000000000 : ℝ)*X 0 0+(5956957439/10000000000 : ℝ)*X 0 1+(4693066503/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328055_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((5366552023/10000000000 : ℝ)*X 1 0+(-186869341/5000000000 : ℝ)*X 1 1+(715300319/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328055_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((433461723/1000000000 : ℝ)*X 2 0+(6017931983/10000000000 : ℝ)*X 2 1+(-22085923/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328055_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((7565849113/10000000000 : ℝ)*X 0 0+(1078376629/5000000000 : ℝ)*X 0 1+(36747641/200000000 : ℝ)*X 0 2+(7565849113/10000000000 : ℝ)*X 1 0+(1078376629/5000000000 : ℝ)*X 1 1+(36747641/200000000 : ℝ)*X 1 2+(7565849113/10000000000 : ℝ)*X 2 0+(1078376629/5000000000 : ℝ)*X 2 1+(36747641/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328055_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((759/2500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(759/2500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1813266812407122551749674993/96389379800000000000000000000000 : ℝ) := by norm_num
    linear_combination (650619/200000000000 : ℝ)*(base19) + (399178140179/500000000000 : ℝ)*(base49) + (376037/1000000000000 : ℝ)*(base60) + (3429065017171/500000000000 : ℝ)*(major_s1_0) + (3429065017171/500000000000 : ℝ)*(major_s1_1) + (3429065017171/500000000000 : ℝ)*(major_s1_2) + (7364423/500000000000 : ℝ)*(sp_s1_2) + (10555389567047/1000000000000 : ℝ)*(sp_s1_7) + (10555364813439/1000000000000 : ℝ)*(sp_s1_8) + (2111056233231/200000000000 : ℝ)*(sp_s1_9) + (3160792733883/1000000000000 : ℝ)*(sp_s1_13) + (446857/6250000000 : ℝ)*(sp_s1_14) + (92997633/1000000000000 : ℝ)*(sp_s1_15) + (82584583/500000000000 : ℝ)*(sp_s1_23) + (3160792733883/1000000000000 : ℝ)*(f.failure) + (10555461064167/1000000000000 : ℝ)*(f.sum) + (110838361321590129029/183673146050000000000000000000000 : ℝ)*base62 + (644542073214741/1527275000000000000000000000 : ℝ)*base65 + (592620567135813/3006550000000000000000000000 : ℝ)*base67 + (407990444184179/1527275000000000000000000000 : ℝ)*base68 + (24504090115262893333/192778759600000000000000000000000 : ℝ)*base71 + (584749963052763/3155600000000000000000000000 : ℝ)*base73 + (203562625171899/3006550000000000000000000000 : ℝ)*base75 + (61425511947199/3155600000000000000000000000 : ℝ)*base77 + (15126926812074904431/189749383600000000000000000000000 : ℝ)*base78 + (2557/4000000000000000 : ℝ)*base87 + (2557/4000000000000000 : ℝ)*base89 + (2557/4000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31089/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31089/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (453179125086892303290729905433/33119941695736000000000000000000000 : ℝ) := by norm_num
    linear_combination (27783/15625000000 : ℝ)*(base39) + (660229705901/1000000000000 : ℝ)*(base49) + (879999/500000000000 : ℝ)*(base60) + (1286427138647/200000000000 : ℝ)*(major_s1_0) + (1286427138647/200000000000 : ℝ)*(major_s1_1) + (1286427138647/200000000000 : ℝ)*(major_s1_2) + (19328399/1000000000000 : ℝ)*(sp_s1_2) + (31485547/500000000000 : ℝ)*(sp_s1_7) + (98229053/1000000000000 : ℝ)*(sp_s1_8) + (9899744495823/1000000000000 : ℝ)*(sp_s1_14) + (1237463654733/125000000000 : ℝ)*(sp_s1_15) + (4949894069259/500000000000 : ℝ)*(sp_s1_16) + (1482206222899/500000000000 : ℝ)*(sp_s1_20) + (23456381/500000000000 : ℝ)*(sp_s1_27) + (18527870991/6250000000 : ℝ)*(f.failure) + (9899807466917/1000000000000 : ℝ)*(f.sum) + (510495532625393/293877033680000000000000000000 : ℝ)*base63 + (62194454830809/122182000000000000000000000 : ℝ)*base64 + (795729499607761/1202620000000000000000000000 : ℝ)*base66 + (460461246773131/1221820000000000000000000000 : ℝ)*base68 + (1405425462187243033/11015929120000000000000000000000 : ℝ)*base70 + (43020040334519/180320000000000000000000000 : ℝ)*base72 + (504431651329167/1202620000000000000000000000 : ℝ)*base74 + (78333756733763/180320000000000000000000000 : ℝ)*base76 + (1180437664449348861/10842821920000000000000000000000 : ℝ)*base78 + (7/12500000000000 : ℝ)*base87 + (7/12500000000000 : ℝ)*base89 + (7/12500000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15019/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15019/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (369918969035775520058667819/27107054800000000000000000000000 : ℝ) := by norm_num
    linear_combination (11901183/1000000000000 : ℝ)*(base15) + (37356205469/1000000000000 : ℝ)*(base40) + (413837894511/500000000000 : ℝ)*(base49) + (1577317/1000000000000 : ℝ)*(base59) + (6343541156211/1000000000000 : ℝ)*(major_s1_0) + (6343541156211/1000000000000 : ℝ)*(major_s1_1) + (6343541156211/1000000000000 : ℝ)*(major_s1_2) + (34106347/1000000000000 : ℝ)*(sp_s1_1) + (18789437/200000000000 : ℝ)*(sp_s1_9) + (45411717/1000000000000 : ℝ)*(sp_s1_20) + (9763450084693/1000000000000 : ℝ)*(sp_s1_21) + (9763404077163/1000000000000 : ℝ)*(sp_s1_22) + (2440839034377/250000000000 : ℝ)*(sp_s1_23) + (584716453429/200000000000 : ℝ)*(sp_s1_27) + (1461813839431/500000000000 : ℝ)*(f.failure) + (9763450084693/1000000000000 : ℝ)*(f.sum) + (2708390641104350267/183673146050000000000000000000000 : ℝ)*base62 + (65851340285821/3054550000000000000000000000 : ℝ)*base65 + (1540670849144863/6013100000000000000000000000 : ℝ)*base67 + (456804306495087/6109100000000000000000000000 : ℝ)*base69 + (18272808171540665901/55079645600000000000000000000000 : ℝ)*base70 + (331339622479389/901600000000000000000000000 : ℝ)*base73 + (777834467170929/6013100000000000000000000000 : ℝ)*base75 + (9954451532737/901600000000000000000000000 : ℝ)*base77 + (15063404415052492127/54214109600000000000000000000000 : ℝ)*base79 + (351/2000000000000000 : ℝ)*base86 + (351/2000000000000000 : ℝ)*base88 + (351/2000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((7889/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7889/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(60131/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(60131/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61091/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(61091/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((759/2500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(759/2500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31089/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(31089/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15019/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15019/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c328055_s1 p hpa hpb X hX hprev0

#print axioms solution
