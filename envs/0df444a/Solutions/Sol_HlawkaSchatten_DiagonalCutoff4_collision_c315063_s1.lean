-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c315063_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:56:50.344513+00:00
-- url     : https://prove2.me/submissions/91c69084-0886-432e-b744-1be66be001ce

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
theorem collision_support_c315063_s1_s1_0 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-680964189/10000000000 : ℝ)*x 0 + (1111143979/2000000000 : ℝ)*x 1 + (35688527/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (680964189/10000000000 : ℝ)^19 ≤ (166313467177/5000000000000 : ℝ)^15 := by
    have hnat : (680964189 : ℕ)^19*5000000000000^15 ≤ 166313467177^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680964189 10000000000 166313467177 5000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1111143979/2000000000 : ℝ)^19 ≤ (47497538055393/100000000000000 : ℝ)^15 := by
    have hnat : (1111143979 : ℕ)^19*100000000000000^15 ≤ 47497538055393^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111143979 2000000000 47497538055393 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35688527/62500000 : ℝ)^19 ≤ (6147024073653/12500000000000 : ℝ)^15 := by
    have hnat : (35688527 : ℕ)^19*12500000000000^15 ≤ 6147024073653^15*62500000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35688527 62500000 6147024073653 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-680964189/10000000000 : ℝ), (1111143979/2000000000 : ℝ), (35688527/62500000 : ℝ)] ![(166313467177/5000000000000 : ℝ), (47497538055393/100000000000000 : ℝ), (6147024073653/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-680964189/10000000000 : ℝ)|^19 ≤ (166313467177/5000000000000 : ℝ)^15
        have hw : |(-680964189/10000000000 : ℝ)|=(680964189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1111143979/2000000000 : ℝ)|^19 ≤ (47497538055393/100000000000000 : ℝ)^15
        have hw : |(1111143979/2000000000 : ℝ)|=(1111143979/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35688527/62500000 : ℝ)|^19 ≤ (6147024073653/12500000000000 : ℝ)^15
        have hw : |(35688527/62500000 : ℝ)|=(35688527/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315063_s1_s1_1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (277769011/500000000 : ℝ)*x 0 + (-672122579/10000000000 : ℝ)*x 1 + (1143101399/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (277769011/500000000 : ℝ)^19 ≤ (47493859704607/100000000000000 : ℝ)^15 := by
    have hnat : (277769011 : ℕ)^19*100000000000000^15 ≤ 47493859704607^15*500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      277769011 500000000 47493859704607 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (672122579/10000000000 : ℝ)^19 ≤ (13086637497/400000000000 : ℝ)^15 := by
    have hnat : (672122579 : ℕ)^19*400000000000^15 ≤ 13086637497^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672122579 10000000000 13086637497 400000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1143101399/2000000000 : ℝ)^19 ≤ (12308620227931/25000000000000 : ℝ)^15 := by
    have hnat : (1143101399 : ℕ)^19*25000000000000^15 ≤ 12308620227931^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1143101399 2000000000 12308620227931 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(277769011/500000000 : ℝ), (-672122579/10000000000 : ℝ), (1143101399/2000000000 : ℝ)] ![(47493859704607/100000000000000 : ℝ), (13086637497/400000000000 : ℝ), (12308620227931/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(277769011/500000000 : ℝ)|^19 ≤ (47493859704607/100000000000000 : ℝ)^15
        have hw : |(277769011/500000000 : ℝ)|=(277769011/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-672122579/10000000000 : ℝ)|^19 ≤ (13086637497/400000000000 : ℝ)^15
        have hw : |(-672122579/10000000000 : ℝ)|=(672122579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1143101399/2000000000 : ℝ)|^19 ≤ (12308620227931/25000000000000 : ℝ)^15
        have hw : |(1143101399/2000000000 : ℝ)|=(1143101399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315063_s1_s1_2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2802079509/5000000000 : ℝ)*x 0 + (1423929643/2500000000 : ℝ)*x 1 + (-124164419/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2802079509/5000000000 : ℝ)^19 ≤ (48022699551123/100000000000000 : ℝ)^15 := by
    have hnat : (2802079509 : ℕ)^19*100000000000000^15 ≤ 48022699551123^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2802079509 5000000000 48022699551123 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1423929643/2500000000 : ℝ)^19 ≤ (9803732605573/20000000000000 : ℝ)^15 := by
    have hnat : (1423929643 : ℕ)^19*20000000000000^15 ≤ 9803732605573^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1423929643 2500000000 9803732605573 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (124164419/2000000000 : ℝ)^19 ≤ (1479318698361/50000000000000 : ℝ)^15 := by
    have hnat : (124164419 : ℕ)^19*50000000000000^15 ≤ 1479318698361^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124164419 2000000000 1479318698361 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2802079509/5000000000 : ℝ), (1423929643/2500000000 : ℝ), (-124164419/2000000000 : ℝ)] ![(48022699551123/100000000000000 : ℝ), (9803732605573/20000000000000 : ℝ), (1479318698361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2802079509/5000000000 : ℝ)|^19 ≤ (48022699551123/100000000000000 : ℝ)^15
        have hw : |(2802079509/5000000000 : ℝ)|=(2802079509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1423929643/2500000000 : ℝ)|^19 ≤ (9803732605573/20000000000000 : ℝ)^15
        have hw : |(1423929643/2500000000 : ℝ)|=(1423929643/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-124164419/2000000000 : ℝ)|^19 ≤ (1479318698361/50000000000000 : ℝ)^15
        have hw : |(-124164419/2000000000 : ℝ)|=(124164419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315063_s1_s1_7 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1201117973/10000000000 : ℝ)*x 0 + (1562764331/5000000000 : ℝ)*x 1 + (7567407013/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1201117973/10000000000 : ℝ)^19 ≤ (6825615863283/100000000000000 : ℝ)^15 := by
    have hnat : (1201117973 : ℕ)^19*100000000000000^15 ≤ 6825615863283^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1201117973 10000000000 6825615863283 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1562764331/5000000000 : ℝ)^19 ≤ (22921150641799/100000000000000 : ℝ)^15 := by
    have hnat : (1562764331 : ℕ)^19*100000000000000^15 ≤ 22921150641799^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1562764331 5000000000 22921150641799 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7567407013/10000000000 : ℝ)^19 ≤ (14050646697773/20000000000000 : ℝ)^15 := by
    have hnat : (7567407013 : ℕ)^19*20000000000000^15 ≤ 14050646697773^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7567407013 10000000000 14050646697773 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1201117973/10000000000 : ℝ), (1562764331/5000000000 : ℝ), (7567407013/10000000000 : ℝ)] ![(6825615863283/100000000000000 : ℝ), (22921150641799/100000000000000 : ℝ), (14050646697773/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1201117973/10000000000 : ℝ)|^19 ≤ (6825615863283/100000000000000 : ℝ)^15
        have hw : |(-1201117973/10000000000 : ℝ)|=(1201117973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1562764331/5000000000 : ℝ)|^19 ≤ (22921150641799/100000000000000 : ℝ)^15
        have hw : |(1562764331/5000000000 : ℝ)|=(1562764331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7567407013/10000000000 : ℝ)|^19 ≤ (14050646697773/20000000000000 : ℝ)^15
        have hw : |(7567407013/10000000000 : ℝ)|=(7567407013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315063_s1_s1_8 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3769270919/10000000000 : ℝ)*x 0 + (-179244219/10000000000 : ℝ)*x 1 + (757385741/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3769270919/10000000000 : ℝ)^19 ≤ (29057571479147/100000000000000 : ℝ)^15 := by
    have hnat : (3769270919 : ℕ)^19*100000000000000^15 ≤ 29057571479147^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3769270919 10000000000 29057571479147 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179244219/10000000000 : ℝ)^19 ≤ (613334225053/100000000000000 : ℝ)^15 := by
    have hnat : (179244219 : ℕ)^19*100000000000000^15 ≤ 613334225053^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179244219 10000000000 613334225053 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (757385741/1000000000 : ℝ)^19 ≤ (35164547139079/50000000000000 : ℝ)^15 := by
    have hnat : (757385741 : ℕ)^19*50000000000000^15 ≤ 35164547139079^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      757385741 1000000000 35164547139079 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3769270919/10000000000 : ℝ), (-179244219/10000000000 : ℝ), (757385741/1000000000 : ℝ)] ![(29057571479147/100000000000000 : ℝ), (613334225053/100000000000000 : ℝ), (35164547139079/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3769270919/10000000000 : ℝ)|^19 ≤ (29057571479147/100000000000000 : ℝ)^15
        have hw : |(3769270919/10000000000 : ℝ)|=(3769270919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-179244219/10000000000 : ℝ)|^19 ≤ (613334225053/100000000000000 : ℝ)^15
        have hw : |(-179244219/10000000000 : ℝ)|=(179244219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(757385741/1000000000 : ℝ)|^19 ≤ (35164547139079/50000000000000 : ℝ)^15
        have hw : |(757385741/1000000000 : ℝ)|=(757385741/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315063_s1_s1_9 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (887128999/2500000000 : ℝ)*x 0 + (7789171911/10000000000 : ℝ)*x 1 + (-76856921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (887128999/2500000000 : ℝ)^19 ≤ (26919019592087/100000000000000 : ℝ)^15 := by
    have hnat : (887128999 : ℕ)^19*100000000000000^15 ≤ 26919019592087^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887128999 2500000000 26919019592087 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7789171911/10000000000 : ℝ)^19 ≤ (36435575796197/50000000000000 : ℝ)^15 := by
    have hnat : (7789171911 : ℕ)^19*50000000000000^15 ≤ 36435575796197^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7789171911 10000000000 36435575796197 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (76856921/10000000000 : ℝ)^19 ≤ (104914403289/50000000000000 : ℝ)^15 := by
    have hnat : (76856921 : ℕ)^19*50000000000000^15 ≤ 104914403289^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76856921 10000000000 104914403289 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(887128999/2500000000 : ℝ), (7789171911/10000000000 : ℝ), (-76856921/10000000000 : ℝ)] ![(26919019592087/100000000000000 : ℝ), (36435575796197/50000000000000 : ℝ), (104914403289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(887128999/2500000000 : ℝ)|^19 ≤ (26919019592087/100000000000000 : ℝ)^15
        have hw : |(887128999/2500000000 : ℝ)|=(887128999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7789171911/10000000000 : ℝ)|^19 ≤ (36435575796197/50000000000000 : ℝ)^15
        have hw : |(7789171911/10000000000 : ℝ)|=(7789171911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-76856921/10000000000 : ℝ)|^19 ≤ (104914403289/50000000000000 : ℝ)^15
        have hw : |(-76856921/10000000000 : ℝ)|=(76856921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315063_s1_s1_13 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (225716339/625000000 : ℝ)*x 0 + (3479806887/5000000000 : ℝ)*x 1 + (383034749/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (225716339/625000000 : ℝ)^19 ≤ (5505056374107/20000000000000 : ℝ)^15 := by
    have hnat : (225716339 : ℕ)^19*20000000000000^15 ≤ 5505056374107^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225716339 625000000 5505056374107 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3479806887/5000000000 : ℝ)^19 ≤ (31592052833471/50000000000000 : ℝ)^15 := by
    have hnat : (3479806887 : ℕ)^19*50000000000000^15 ≤ 31592052833471^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3479806887 5000000000 31592052833471 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (383034749/2500000000 : ℝ)^19 ≤ (4645306223399/50000000000000 : ℝ)^15 := by
    have hnat : (383034749 : ℕ)^19*50000000000000^15 ≤ 4645306223399^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      383034749 2500000000 4645306223399 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(225716339/625000000 : ℝ), (3479806887/5000000000 : ℝ), (383034749/2500000000 : ℝ)] ![(5505056374107/20000000000000 : ℝ), (31592052833471/50000000000000 : ℝ), (4645306223399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(225716339/625000000 : ℝ)|^19 ≤ (5505056374107/20000000000000 : ℝ)^15
        have hw : |(225716339/625000000 : ℝ)|=(225716339/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3479806887/5000000000 : ℝ)|^19 ≤ (31592052833471/50000000000000 : ℝ)^15
        have hw : |(3479806887/5000000000 : ℝ)|=(3479806887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(383034749/2500000000 : ℝ)|^19 ≤ (4645306223399/50000000000000 : ℝ)^15
        have hw : |(383034749/2500000000 : ℝ)|=(383034749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315063_s1_s1_14 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-10350119/625000000 : ℝ)*x 0 + (1846697131/5000000000 : ℝ)*x 1 + (7641575093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10350119/625000000 : ℝ)^19 ≤ (554816556601/100000000000000 : ℝ)^15 := by
    have hnat : (10350119 : ℕ)^19*100000000000000^15 ≤ 554816556601^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10350119 625000000 554816556601 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1846697131/5000000000 : ℝ)^19 ≤ (5663729603331/20000000000000 : ℝ)^15 := by
    have hnat : (1846697131 : ℕ)^19*20000000000000^15 ≤ 5663729603331^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1846697131 5000000000 5663729603331 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7641575093/10000000000 : ℝ)^19 ≤ (14225307082181/20000000000000 : ℝ)^15 := by
    have hnat : (7641575093 : ℕ)^19*20000000000000^15 ≤ 14225307082181^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7641575093 10000000000 14225307082181 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-10350119/625000000 : ℝ), (1846697131/5000000000 : ℝ), (7641575093/10000000000 : ℝ)] ![(554816556601/100000000000000 : ℝ), (5663729603331/20000000000000 : ℝ), (14225307082181/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-10350119/625000000 : ℝ)|^19 ≤ (554816556601/100000000000000 : ℝ)^15
        have hw : |(-10350119/625000000 : ℝ)|=(10350119/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1846697131/5000000000 : ℝ)|^19 ≤ (5663729603331/20000000000000 : ℝ)^15
        have hw : |(1846697131/5000000000 : ℝ)|=(1846697131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7641575093/10000000000 : ℝ)|^19 ≤ (14225307082181/20000000000000 : ℝ)^15
        have hw : |(7641575093/10000000000 : ℝ)|=(7641575093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315063_s1_s1_15 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (301503947/1000000000 : ℝ)*x 0 + (-1210984869/10000000000 : ℝ)*x 1 + (7648110977/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (301503947/1000000000 : ℝ)^19 ≤ (21899681686361/100000000000000 : ℝ)^15 := by
    have hnat : (301503947 : ℕ)^19*100000000000000^15 ≤ 21899681686361^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301503947 1000000000 21899681686361 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1210984869/10000000000 : ℝ)^19 ≤ (689671650857/10000000000000 : ℝ)^15 := by
    have hnat : (1210984869 : ℕ)^19*10000000000000^15 ≤ 689671650857^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1210984869 10000000000 689671650857 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7648110977/10000000000 : ℝ)^19 ≤ (7120360179117/10000000000000 : ℝ)^15 := by
    have hnat : (7648110977 : ℕ)^19*10000000000000^15 ≤ 7120360179117^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7648110977 10000000000 7120360179117 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(301503947/1000000000 : ℝ), (-1210984869/10000000000 : ℝ), (7648110977/10000000000 : ℝ)] ![(21899681686361/100000000000000 : ℝ), (689671650857/10000000000000 : ℝ), (7120360179117/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(301503947/1000000000 : ℝ)|^19 ≤ (21899681686361/100000000000000 : ℝ)^15
        have hw : |(301503947/1000000000 : ℝ)|=(301503947/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1210984869/10000000000 : ℝ)|^19 ≤ (689671650857/10000000000000 : ℝ)^15
        have hw : |(-1210984869/10000000000 : ℝ)|=(1210984869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(7648110977/10000000000 : ℝ)|^19 ≤ (7120360179117/10000000000000 : ℝ)^15
        have hw : |(7648110977/10000000000 : ℝ)|=(7648110977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315063_s1_s1_16 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7521213501/10000000000 : ℝ)*x 0 + (1932307863/5000000000 : ℝ)*x 1 + (-50665387/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7521213501/10000000000 : ℝ)^19 ≤ (69710472778729/100000000000000 : ℝ)^15 := by
    have hnat : (7521213501 : ℕ)^19*100000000000000^15 ≤ 69710472778729^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7521213501 10000000000 69710472778729 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1932307863/5000000000 : ℝ)^19 ≤ (7497929338723/25000000000000 : ℝ)^15 := by
    have hnat : (1932307863 : ℕ)^19*25000000000000^15 ≤ 7497929338723^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1932307863 5000000000 7497929338723 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50665387/5000000000 : ℝ)^19 ≤ (74452462173/25000000000000 : ℝ)^15 := by
    have hnat : (50665387 : ℕ)^19*25000000000000^15 ≤ 74452462173^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50665387 5000000000 74452462173 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7521213501/10000000000 : ℝ), (1932307863/5000000000 : ℝ), (-50665387/5000000000 : ℝ)] ![(69710472778729/100000000000000 : ℝ), (7497929338723/25000000000000 : ℝ), (74452462173/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7521213501/10000000000 : ℝ)|^19 ≤ (69710472778729/100000000000000 : ℝ)^15
        have hw : |(7521213501/10000000000 : ℝ)|=(7521213501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1932307863/5000000000 : ℝ)|^19 ≤ (7497929338723/25000000000000 : ℝ)^15
        have hw : |(1932307863/5000000000 : ℝ)|=(1932307863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-50665387/5000000000 : ℝ)|^19 ≤ (74452462173/25000000000000 : ℝ)^15
        have hw : |(-50665387/5000000000 : ℝ)|=(50665387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315063_s1_s1_20 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7440635737/10000000000 : ℝ)*x 0 + (3030851963/10000000000 : ℝ)*x 1 + (1518881313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7440635737/10000000000 : ℝ)^19 ≤ (2148932350063/3125000000000 : ℝ)^15 := by
    have hnat : (7440635737 : ℕ)^19*3125000000000^15 ≤ 2148932350063^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7440635737 10000000000 2148932350063 3125000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3030851963/10000000000 : ℝ)^19 ≤ (11022632346487/50000000000000 : ℝ)^15 := by
    have hnat : (3030851963 : ℕ)^19*50000000000000^15 ≤ 11022632346487^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3030851963 10000000000 11022632346487 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1518881313/10000000000 : ℝ)^19 ≤ (9188900086479/100000000000000 : ℝ)^15 := by
    have hnat : (1518881313 : ℕ)^19*100000000000000^15 ≤ 9188900086479^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1518881313 10000000000 9188900086479 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7440635737/10000000000 : ℝ), (3030851963/10000000000 : ℝ), (1518881313/10000000000 : ℝ)] ![(2148932350063/3125000000000 : ℝ), (11022632346487/50000000000000 : ℝ), (9188900086479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7440635737/10000000000 : ℝ)|^19 ≤ (2148932350063/3125000000000 : ℝ)^15
        have hw : |(7440635737/10000000000 : ℝ)|=(7440635737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3030851963/10000000000 : ℝ)|^19 ≤ (11022632346487/50000000000000 : ℝ)^15
        have hw : |(3030851963/10000000000 : ℝ)|=(3030851963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1518881313/10000000000 : ℝ)|^19 ≤ (9188900086479/100000000000000 : ℝ)^15
        have hw : |(1518881313/10000000000 : ℝ)|=(1518881313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315063_s1_s1_21 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-19429779/1250000000 : ℝ)*x 0 + (3439073291/5000000000 : ℝ)*x 1 + (458475713/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19429779/1250000000 : ℝ)^19 ≤ (512043204977/100000000000000 : ℝ)^15 := by
    have hnat : (19429779 : ℕ)^19*100000000000000^15 ≤ 512043204977^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19429779 1250000000 512043204977 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3439073291/5000000000 : ℝ)^19 ≤ (2489949078243/4000000000000 : ℝ)^15 := by
    have hnat : (3439073291 : ℕ)^19*4000000000000^15 ≤ 2489949078243^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3439073291 5000000000 2489949078243 4000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (458475713/1000000000 : ℝ)^19 ≤ (232745186439/625000000000 : ℝ)^15 := by
    have hnat : (458475713 : ℕ)^19*625000000000^15 ≤ 232745186439^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458475713 1000000000 232745186439 625000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-19429779/1250000000 : ℝ), (3439073291/5000000000 : ℝ), (458475713/1000000000 : ℝ)] ![(512043204977/100000000000000 : ℝ), (2489949078243/4000000000000 : ℝ), (232745186439/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-19429779/1250000000 : ℝ)|^19 ≤ (512043204977/100000000000000 : ℝ)^15
        have hw : |(-19429779/1250000000 : ℝ)|=(19429779/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3439073291/5000000000 : ℝ)|^19 ≤ (2489949078243/4000000000000 : ℝ)^15
        have hw : |(3439073291/5000000000 : ℝ)|=(3439073291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(458475713/1000000000 : ℝ)|^19 ≤ (232745186439/625000000000 : ℝ)^15
        have hw : |(458475713/1000000000 : ℝ)|=(458475713/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315063_s1_s1_22 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7516811313/10000000000 : ℝ)*x 0 + (-18152673/2500000000 : ℝ)*x 1 + (388029721/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7516811313/10000000000 : ℝ)^19 ≤ (17414698651773/25000000000000 : ℝ)^15 := by
    have hnat : (7516811313 : ℕ)^19*25000000000000^15 ≤ 17414698651773^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7516811313 10000000000 17414698651773 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (18152673/2500000000 : ℝ)^19 ≤ (195254354993/100000000000000 : ℝ)^15 := by
    have hnat : (18152673 : ℕ)^19*100000000000000^15 ≤ 195254354993^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18152673 2500000000 195254354993 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (388029721/1000000000 : ℝ)^19 ≤ (6029190204661/20000000000000 : ℝ)^15 := by
    have hnat : (388029721 : ℕ)^19*20000000000000^15 ≤ 6029190204661^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388029721 1000000000 6029190204661 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7516811313/10000000000 : ℝ), (-18152673/2500000000 : ℝ), (388029721/1000000000 : ℝ)] ![(17414698651773/25000000000000 : ℝ), (195254354993/100000000000000 : ℝ), (6029190204661/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7516811313/10000000000 : ℝ)|^19 ≤ (17414698651773/25000000000000 : ℝ)^15
        have hw : |(7516811313/10000000000 : ℝ)|=(7516811313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-18152673/2500000000 : ℝ)|^19 ≤ (195254354993/100000000000000 : ℝ)^15
        have hw : |(-18152673/2500000000 : ℝ)|=(18152673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(388029721/1000000000 : ℝ)|^19 ≤ (6029190204661/20000000000000 : ℝ)^15
        have hw : |(388029721/1000000000 : ℝ)|=(388029721/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315063_s1_s1_23 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (724129041/2500000000 : ℝ)*x 0 + (388070653/500000000 : ℝ)*x 1 + (-587813463/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (724129041/2500000000 : ℝ)^19 ≤ (5203747558577/25000000000000 : ℝ)^15 := by
    have hnat : (724129041 : ℕ)^19*25000000000000^15 ≤ 5203747558577^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      724129041 2500000000 5203747558577 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (388070653/500000000 : ℝ)^19 ≤ (72542359337581/100000000000000 : ℝ)^15 := by
    have hnat : (388070653 : ℕ)^19*100000000000000^15 ≤ 72542359337581^15*500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388070653 500000000 72542359337581 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (587813463/5000000000 : ℝ)^19 ≤ (3321325209627/50000000000000 : ℝ)^15 := by
    have hnat : (587813463 : ℕ)^19*50000000000000^15 ≤ 3321325209627^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      587813463 5000000000 3321325209627 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(724129041/2500000000 : ℝ), (388070653/500000000 : ℝ), (-587813463/5000000000 : ℝ)] ![(5203747558577/25000000000000 : ℝ), (72542359337581/100000000000000 : ℝ), (3321325209627/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(724129041/2500000000 : ℝ)|^19 ≤ (5203747558577/25000000000000 : ℝ)^15
        have hw : |(724129041/2500000000 : ℝ)|=(724129041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(388070653/500000000 : ℝ)|^19 ≤ (72542359337581/100000000000000 : ℝ)^15
        have hw : |(388070653/500000000 : ℝ)|=(388070653/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-587813463/5000000000 : ℝ)|^19 ≤ (3321325209627/50000000000000 : ℝ)^15
        have hw : |(-587813463/5000000000 : ℝ)|=(587813463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315063_s1_s1_27 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (151806581/200000000 : ℝ)*x 0 + (1227030511/5000000000 : ℝ)*x 1 + (389863409/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (151806581/200000000 : ℝ)^19 ≤ (3526144472043/5000000000000 : ℝ)^15 := by
    have hnat : (151806581 : ℕ)^19*5000000000000^15 ≤ 3526144472043^15*200000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151806581 200000000 3526144472043 5000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1227030511/5000000000 : ℝ)^19 ≤ (16872837332439/100000000000000 : ℝ)^15 := by
    have hnat : (1227030511 : ℕ)^19*100000000000000^15 ≤ 16872837332439^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1227030511 5000000000 16872837332439 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (389863409/2000000000 : ℝ)^19 ≤ (12604273211079/100000000000000 : ℝ)^15 := by
    have hnat : (389863409 : ℕ)^19*100000000000000^15 ≤ 12604273211079^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389863409 2000000000 12604273211079 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(151806581/200000000 : ℝ), (1227030511/5000000000 : ℝ), (389863409/2000000000 : ℝ)] ![(3526144472043/5000000000000 : ℝ), (16872837332439/100000000000000 : ℝ), (12604273211079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(151806581/200000000 : ℝ)|^19 ≤ (3526144472043/5000000000000 : ℝ)^15
        have hw : |(151806581/200000000 : ℝ)|=(151806581/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1227030511/5000000000 : ℝ)|^19 ≤ (16872837332439/100000000000000 : ℝ)^15
        have hw : |(1227030511/5000000000 : ℝ)|=(1227030511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(389863409/2000000000 : ℝ)|^19 ≤ (12604273211079/100000000000000 : ℝ)^15
        have hw : |(389863409/2000000000 : ℝ)|=(389863409/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c315063_s1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((79709/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(79709/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3173/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3173/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3853/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3853/5000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((60727/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(60727/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61001/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(61001/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5853/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5853/10000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15821/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15821/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15821/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15821/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (34911/20000 : ℝ) := by
    linarith only [f.Tcap]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (79709/100000 : ℝ) ^ (75/16 : ℝ) ≤ (431743458483598213/1250000000000000000 : ℝ) := by
    have hpowers : (79709/100000 : ℝ)^75 ≤ (431743458483598213/1250000000000000000 : ℝ)^16 := by
      have hnat : (79709 : ℕ)^75*1250000000000000000^16 ≤ 431743458483598213^16*100000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79709 100000 431743458483598213 1250000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (79709/100000 : ℝ)) (X := (431743458483598213/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (1681743458483598213/1250000000000000000 : ℝ) ≤ (10653392876770519/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (1681743458483598213/1250000000000000000 : ℝ)^16 ≤ (10653392876770519/10000000000000000 : ℝ)^75 := by
      have hnat : (1681743458483598213 : ℕ)^16*10000000000000000^75 ≤ 10653392876770519^75*1250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1681743458483598213 1250000000000000000 10653392876770519 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10653392876770519/10000000000000000 : ℝ)) (X := (1681743458483598213/1250000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (1056743458483598213/625000000000000000 : ℝ) ≤ (349549854624071/312500000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (1056743458483598213/625000000000000000 : ℝ)^16 ≤ (349549854624071/312500000000000 : ℝ)^75 := by
      have hnat : (1056743458483598213 : ℕ)^16*312500000000000^75 ≤ 349549854624071^75*625000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1056743458483598213 625000000000000000 349549854624071 312500000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (349549854624071/312500000000000 : ℝ)) (X := (1056743458483598213/625000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(653392876770519/7970900000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(532202471199753/7970900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (79709/100000 : ℝ)) (alpha := (653392876770519/7970900000000000 : ℝ)) (beta := (532202471199753/7970900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (79709/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(653392876770519/7970900000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(532202471199753/7970900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (3173/4000 : ℝ) ^ (75/16 : ℝ) ≤ (33766399437295494409/100000000000000000000 : ℝ) := by
    have hpowers : (3173/4000 : ℝ)^75 ≤ (33766399437295494409/100000000000000000000 : ℝ)^16 := by
      have hnat : (3173 : ℕ)^75*100000000000000000000^16 ≤ 33766399437295494409^16*4000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3173 4000 33766399437295494409 100000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3173/4000 : ℝ)) (X := (33766399437295494409/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (133766399437295494409/100000000000000000000 : ℝ) ≤ (10640303962078233/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (133766399437295494409/100000000000000000000 : ℝ)^16 ≤ (10640303962078233/10000000000000000 : ℝ)^75 := by
      have hnat : (133766399437295494409 : ℕ)^16*10000000000000000^75 ≤ 10640303962078233^75*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        133766399437295494409 100000000000000000000 10640303962078233 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10640303962078233/10000000000000000 : ℝ)) (X := (133766399437295494409/100000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (83766399437295494409/50000000000000000000 : ℝ) ≤ (5581847551227699/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (83766399437295494409/50000000000000000000 : ℝ)^16 ≤ (5581847551227699/5000000000000000 : ℝ)^75 := by
      have hnat : (83766399437295494409 : ℕ)^16*5000000000000000^75 ≤ 5581847551227699^75*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        83766399437295494409 50000000000000000000 5581847551227699 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5581847551227699/5000000000000000 : ℝ)) (X := (83766399437295494409/50000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(640303962078233/7932500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(104678228075433/1586500000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (3173/4000 : ℝ)) (alpha := (640303962078233/7932500000000000 : ℝ)) (beta := (104678228075433/1586500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (3173/4000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(640303962078233/7932500000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(104678228075433/1586500000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (3853/5000 : ℝ) ^ (75/16 : ℝ) ≤ (2947887865632475181/10000000000000000000 : ℝ) := by
    have hpowers : (3853/5000 : ℝ)^75 ≤ (2947887865632475181/10000000000000000000 : ℝ)^16 := by
      have hnat : (3853 : ℕ)^75*10000000000000000000^16 ≤ 2947887865632475181^16*5000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3853 5000 2947887865632475181 10000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3853/5000 : ℝ)) (X := (2947887865632475181/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (12947887865632475181/10000000000000000000 : ℝ) ≤ (5283306133475177/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (12947887865632475181/10000000000000000000 : ℝ)^16 ≤ (5283306133475177/5000000000000000 : ℝ)^75 := by
      have hnat : (12947887865632475181 : ℕ)^16*5000000000000000^75 ≤ 5283306133475177^75*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12947887865632475181 10000000000000000000 5283306133475177 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5283306133475177/5000000000000000 : ℝ)) (X := (12947887865632475181/10000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (7947887865632475181/5000000000000000000 : ℝ) ≤ (11039263549014023/10000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (7947887865632475181/5000000000000000000 : ℝ)^16 ≤ (11039263549014023/10000000000000000 : ℝ)^75 := by
      have hnat : (7947887865632475181 : ℕ)^16*10000000000000000^75 ≤ 11039263549014023^75*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7947887865632475181 5000000000000000000 11039263549014023 10000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11039263549014023/10000000000000000 : ℝ)) (X := (7947887865632475181/5000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(283306133475177/3853000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(472651282063669/7706000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (3853/5000 : ℝ)) (alpha := (283306133475177/3853000000000000 : ℝ)) (beta := (472651282063669/7706000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (3853/5000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(283306133475177/3853000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(472651282063669/7706000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-680964189/10000000000 : ℝ)*X 0 0+(1111143979/2000000000 : ℝ)*X 0 1+(35688527/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315063_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((277769011/500000000 : ℝ)*X 1 0+(-672122579/10000000000 : ℝ)*X 1 1+(1143101399/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315063_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2802079509/5000000000 : ℝ)*X 2 0+(1423929643/2500000000 : ℝ)*X 2 1+(-124164419/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315063_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1201117973/10000000000 : ℝ)*X 0 0+(1562764331/5000000000 : ℝ)*X 0 1+(7567407013/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315063_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((3769270919/10000000000 : ℝ)*X 1 0+(-179244219/10000000000 : ℝ)*X 1 1+(757385741/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315063_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((887128999/2500000000 : ℝ)*X 2 0+(7789171911/10000000000 : ℝ)*X 2 1+(-76856921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315063_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((225716339/625000000 : ℝ)*X 0 0+(3479806887/5000000000 : ℝ)*X 0 1+(383034749/2500000000 : ℝ)*X 0 2+(225716339/625000000 : ℝ)*X 1 0+(3479806887/5000000000 : ℝ)*X 1 1+(383034749/2500000000 : ℝ)*X 1 2+(225716339/625000000 : ℝ)*X 2 0+(3479806887/5000000000 : ℝ)*X 2 1+(383034749/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315063_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-10350119/625000000 : ℝ)*X 0 0+(1846697131/5000000000 : ℝ)*X 0 1+(7641575093/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315063_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((301503947/1000000000 : ℝ)*X 1 0+(-1210984869/10000000000 : ℝ)*X 1 1+(7648110977/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315063_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((7521213501/10000000000 : ℝ)*X 2 0+(1932307863/5000000000 : ℝ)*X 2 1+(-50665387/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315063_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((7440635737/10000000000 : ℝ)*X 0 0+(3030851963/10000000000 : ℝ)*X 0 1+(1518881313/10000000000 : ℝ)*X 0 2+(7440635737/10000000000 : ℝ)*X 1 0+(3030851963/10000000000 : ℝ)*X 1 1+(1518881313/10000000000 : ℝ)*X 1 2+(7440635737/10000000000 : ℝ)*X 2 0+(3030851963/10000000000 : ℝ)*X 2 1+(1518881313/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315063_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-19429779/1250000000 : ℝ)*X 0 0+(3439073291/5000000000 : ℝ)*X 0 1+(458475713/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315063_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((7516811313/10000000000 : ℝ)*X 1 0+(-18152673/2500000000 : ℝ)*X 1 1+(388029721/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315063_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((724129041/2500000000 : ℝ)*X 2 0+(388070653/500000000 : ℝ)*X 2 1+(-587813463/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315063_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((151806581/200000000 : ℝ)*X 0 0+(1227030511/5000000000 : ℝ)*X 0 1+(389863409/2000000000 : ℝ)*X 0 2+(151806581/200000000 : ℝ)*X 1 0+(1227030511/5000000000 : ℝ)*X 1 1+(389863409/2000000000 : ℝ)*X 1 2+(151806581/200000000 : ℝ)*X 2 0+(1227030511/5000000000 : ℝ)*X 2 1+(389863409/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315063_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((60727/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(60727/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (342876878519833366489167323451/69606277101500000000000000000000000 : ℝ) := by norm_num
    linear_combination (172533477157/250000000000 : ℝ)*(base7) + (702103/1000000000000 : ℝ)*(base23) + (339503/1000000000000 : ℝ)*(base50) + (33174231913/500000000000 : ℝ)*(base60) + (971682829733/500000000000 : ℝ)*(major_s1_0) + (971682829733/500000000000 : ℝ)*(major_s1_1) + (971682829733/500000000000 : ℝ)*(major_s1_2) + (3615521/1000000000000 : ℝ)*(sp_s1_0) + (474497678161/200000000000 : ℝ)*(sp_s1_7) + (118625624839/50000000000 : ℝ)*(sp_s1_8) + (2372511534297/1000000000000 : ℝ)*(sp_s1_9) + (901398337027/500000000000 : ℝ)*(sp_s1_13) + (10245227/500000000000 : ℝ)*(sp_s1_14) + (260381/1000000000000 : ℝ)*(sp_s1_23) + (556331382713/500000000000 : ℝ)*(f.failure) + (118625624839/50000000000 : ℝ)*(f.sum) + (7166299568921071501/30563922500000000000000000000000 : ℝ)*base62 + (4417316750520677/3853000000000000000000000000 : ℝ)*base65 + (273224696374157/396625000000000000000000000 : ℝ)*base67 + (349082807650341/1926500000000000000000000000 : ℝ)*base69 + (33089329355362629959/43874111000000000000000000000000 : ℝ)*base71 + (394738195528667/569350000000000000000000000 : ℝ)*base73 + (1565802221099789/3966250000000000000000000000 : ℝ)*base75 + (10464703855389/142337500000000000000000000 : ℝ)*base77 + (554208328077694323/9032737750000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (30133/50000000000000000 : ℝ)*base86 + (30133/50000000000000000 : ℝ)*base88 + (30133/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61001/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(61001/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4610586028492331073915344926407/348031385507500000000000000000000000 : ℝ) := by norm_num
    linear_combination (28500404611/40000000000 : ℝ)*(base7) + (79127/250000000000 : ℝ)*(base39) + (200371/200000000000 : ℝ)*(base49) + (932968014447/500000000000 : ℝ)*(major_s1_0) + (932968014447/500000000000 : ℝ)*(major_s1_1) + (932968014447/500000000000 : ℝ)*(major_s1_2) + (3861589/1000000000000 : ℝ)*(sp_s1_1) + (13403127/250000000000 : ℝ)*(sp_s1_8) + (2248962339937/1000000000000 : ℝ)*(sp_s1_14) + (44978105577/20000000000 : ℝ)*(sp_s1_15) + (1124481376473/500000000000 : ℝ)*(sp_s1_16) + (1780786245923/1000000000000 : ℝ)*(sp_s1_20) + (413009/1000000000000 : ℝ)*(sp_s1_21) + (27373873/500000000000 : ℝ)*(sp_s1_27) + (534165439197/500000000000 : ℝ)*(f.failure) + (1124481376473/500000000000 : ℝ)*(f.sum) + (1942320875150760209/30563922500000000000000000000000 : ℝ)*base62 + (9754114523143/3853000000000000000000000000 : ℝ)*base65 + (311246195907051/793250000000000000000000000 : ℝ)*base67 + (1076664474417831/1926500000000000000000000000 : ℝ)*base68 + (466333239595973781/43874111000000000000000000000000 : ℝ)*base71 + (617319347861977/569350000000000000000000000 : ℝ)*base72 + (12794494132737/1983125000000000000000000000 : ℝ)*base74 + (1101630735353/17792187500000000000000000 : ℝ)*base76 + (15344802792742393/9032737750000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (8823/50000000000000000 : ℝ)*base87 + (8823/50000000000000000 : ℝ)*base89 + (8823/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5853/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5853/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3778060834721472744053113390119/243621969855250000000000000000000000 : ℝ) := by norm_num
    linear_combination (351313347803/500000000000 : ℝ)*(base7) + (151917928811/1000000000000 : ℝ)*(base40) + (1297149/1000000000000 : ℝ)*(base49) + (89161223577/50000000000 : ℝ)*(major_s1_0) + (89161223577/50000000000 : ℝ)*(major_s1_1) + (89161223577/50000000000 : ℝ)*(major_s1_2) + (18051851/1000000000000 : ℝ)*(sp_s1_1) + (24198411/1000000000000 : ℝ)*(sp_s1_2) + (40123741/500000000000 : ℝ)*(sp_s1_9) + (16166629/1000000000000 : ℝ)*(sp_s1_20) + (427329115241/200000000000 : ℝ)*(sp_s1_21) + (1068313762177/500000000000 : ℝ)*(sp_s1_22) + (267067641289/125000000000 : ℝ)*(sp_s1_23) + (1723585383717/1000000000000 : ℝ)*(sp_s1_27) + (51048742737/50000000000 : ℝ)*(f.failure) + (427329115241/200000000000 : ℝ)*(f.sum) + (430896196525579311/764098062500000000000000000000 : ℝ)*base62 + (37503323616183/385300000000000000000000000 : ℝ)*base65 + (9513343506199/79325000000000000000000000 : ℝ)*base66 + (10418352304949/48162500000000000000000000 : ℝ)*base68 + (10626295557619256083/30711877700000000000000000000000 : ℝ)*base70 + (195510064469019/797090000000000000000000000 : ℝ)*base73 + (239552817764943/793250000000000000000000000 : ℝ)*base74 + (75351362093309/797090000000000000000000000 : ℝ)*base76 + (2861615787952422287/12645832850000000000000000000000 : ℝ)*base78 + (1683/5000000000000000 : ℝ)*base87 + (1683/5000000000000000 : ℝ)*base89 + (1683/5000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((79709/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(79709/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3173/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3173/4000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3853/5000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(3853/5000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((60727/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(60727/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(61001/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(61001/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5853/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5853/10000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c315063_s1 p hpa hpb X hX hprev0

#print axioms solution
