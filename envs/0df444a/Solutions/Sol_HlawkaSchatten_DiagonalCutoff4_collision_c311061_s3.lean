-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c311061_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:01:20.23046+00:00
-- url     : https://prove2.me/submissions/cabddcf7-1902-4047-ade2-f86785a2f8c9

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
theorem collision_support_c311061_s3_s3_0 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-2230947287/10000000000 : ℝ)*x 0 + (1126202113/2500000000 : ℝ)*x 1 + (5796119303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2230947287/10000000000 : ℝ)^9 ≤ (14532602578359/100000000000000 : ℝ)^7 := by
    have hnat : (2230947287 : ℕ)^9*100000000000000^7 ≤ 14532602578359^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2230947287 10000000000 14532602578359 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126202113/2500000000 : ℝ)^9 ≤ (7173922895039/20000000000000 : ℝ)^7 := by
    have hnat : (1126202113 : ℕ)^9*20000000000000^7 ≤ 7173922895039^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126202113 2500000000 7173922895039 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5796119303/10000000000 : ℝ)^9 ≤ (49597782930821/100000000000000 : ℝ)^7 := by
    have hnat : (5796119303 : ℕ)^9*100000000000000^7 ≤ 49597782930821^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5796119303 10000000000 49597782930821 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2230947287/10000000000 : ℝ), (1126202113/2500000000 : ℝ), (5796119303/10000000000 : ℝ)] ![(14532602578359/100000000000000 : ℝ), (7173922895039/20000000000000 : ℝ), (49597782930821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2230947287/10000000000 : ℝ)|^9 ≤ (14532602578359/100000000000000 : ℝ)^7
        have hw : |(-2230947287/10000000000 : ℝ)|=(2230947287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1126202113/2500000000 : ℝ)|^9 ≤ (7173922895039/20000000000000 : ℝ)^7
        have hw : |(1126202113/2500000000 : ℝ)|=(1126202113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5796119303/10000000000 : ℝ)|^9 ≤ (49597782930821/100000000000000 : ℝ)^7
        have hw : |(5796119303/10000000000 : ℝ)|=(5796119303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s3_s3_1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4687931263/10000000000 : ℝ)*x 0 + (-2315116183/10000000000 : ℝ)*x 1 + (5558923271/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4687931263/10000000000 : ℝ)^9 ≤ (37755121639921/100000000000000 : ℝ)^7 := by
    have hnat : (4687931263 : ℕ)^9*100000000000000^7 ≤ 37755121639921^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4687931263 10000000000 37755121639921 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2315116183/10000000000 : ℝ)^9 ≤ (7620652597167/50000000000000 : ℝ)^7 := by
    have hnat : (2315116183 : ℕ)^9*50000000000000^7 ≤ 7620652597167^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2315116183 10000000000 7620652597167 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5558923271/10000000000 : ℝ)^9 ≤ (23501786577937/50000000000000 : ℝ)^7 := by
    have hnat : (5558923271 : ℕ)^9*50000000000000^7 ≤ 23501786577937^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5558923271 10000000000 23501786577937 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4687931263/10000000000 : ℝ), (-2315116183/10000000000 : ℝ), (5558923271/10000000000 : ℝ)] ![(37755121639921/100000000000000 : ℝ), (7620652597167/50000000000000 : ℝ), (23501786577937/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4687931263/10000000000 : ℝ)|^9 ≤ (37755121639921/100000000000000 : ℝ)^7
        have hw : |(4687931263/10000000000 : ℝ)|=(4687931263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2315116183/10000000000 : ℝ)|^9 ≤ (7620652597167/50000000000000 : ℝ)^7
        have hw : |(-2315116183/10000000000 : ℝ)|=(2315116183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5558923271/10000000000 : ℝ)|^9 ≤ (23501786577937/50000000000000 : ℝ)^7
        have hw : |(5558923271/10000000000 : ℝ)|=(5558923271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s3_s3_2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1188991811/2500000000 : ℝ)*x 0 + (77130919/125000000 : ℝ)*x 1 + (-85808329/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1188991811/2500000000 : ℝ)^9 ≤ (9615267997667/25000000000000 : ℝ)^7 := by
    have hnat : (1188991811 : ℕ)^9*25000000000000^7 ≤ 9615267997667^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1188991811 2500000000 9615267997667 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (77130919/125000000 : ℝ)^9 ≤ (53753839580679/100000000000000 : ℝ)^7 := by
    have hnat : (77130919 : ℕ)^9*100000000000000^7 ≤ 53753839580679^7*125000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77130919 125000000 53753839580679 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85808329/625000000 : ℝ)^9 ≤ (97313605263/1250000000000 : ℝ)^7 := by
    have hnat : (85808329 : ℕ)^9*1250000000000^7 ≤ 97313605263^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85808329 625000000 97313605263 1250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1188991811/2500000000 : ℝ), (77130919/125000000 : ℝ), (-85808329/625000000 : ℝ)] ![(9615267997667/25000000000000 : ℝ), (53753839580679/100000000000000 : ℝ), (97313605263/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1188991811/2500000000 : ℝ)|^9 ≤ (9615267997667/25000000000000 : ℝ)^7
        have hw : |(1188991811/2500000000 : ℝ)|=(1188991811/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(77130919/125000000 : ℝ)|^9 ≤ (53753839580679/100000000000000 : ℝ)^7
        have hw : |(77130919/125000000 : ℝ)|=(77130919/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-85808329/625000000 : ℝ)|^9 ≤ (97313605263/1250000000000 : ℝ)^7
        have hw : |(-85808329/625000000 : ℝ)|=(85808329/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s3_s3_6 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1503739991/2500000000 : ℝ)*x 0 + (2988907241/10000000000 : ℝ)*x 1 + (898133981/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1503739991/2500000000 : ℝ)^9 ≤ (1040366542051/2000000000000 : ℝ)^7 := by
    have hnat : (1503739991 : ℕ)^9*2000000000000^7 ≤ 1040366542051^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1503739991 2500000000 1040366542051 2000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2988907241/10000000000 : ℝ)^9 ≤ (10583488741101/50000000000000 : ℝ)^7 := by
    have hnat : (2988907241 : ℕ)^9*50000000000000^7 ≤ 10583488741101^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2988907241 10000000000 10583488741101 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (898133981/2500000000 : ℝ)^9 ≤ (5362939081041/20000000000000 : ℝ)^7 := by
    have hnat : (898133981 : ℕ)^9*20000000000000^7 ≤ 5362939081041^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898133981 2500000000 5362939081041 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1503739991/2500000000 : ℝ), (2988907241/10000000000 : ℝ), (898133981/2500000000 : ℝ)] ![(1040366542051/2000000000000 : ℝ), (10583488741101/50000000000000 : ℝ), (5362939081041/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1503739991/2500000000 : ℝ)|^9 ≤ (1040366542051/2000000000000 : ℝ)^7
        have hw : |(1503739991/2500000000 : ℝ)|=(1503739991/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2988907241/10000000000 : ℝ)|^9 ≤ (10583488741101/50000000000000 : ℝ)^7
        have hw : |(2988907241/10000000000 : ℝ)|=(2988907241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(898133981/2500000000 : ℝ)|^9 ≤ (5362939081041/20000000000000 : ℝ)^7
        have hw : |(898133981/2500000000 : ℝ)|=(898133981/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s3_s3_7 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-69899311/312500000 : ℝ)*x 0 + (1968676649/5000000000 : ℝ)*x 1 + (6303681659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (69899311/312500000 : ℝ)^9 ≤ (14581454164113/100000000000000 : ℝ)^7 := by
    have hnat : (69899311 : ℕ)^9*100000000000000^7 ≤ 14581454164113^7*312500000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69899311 312500000 14581454164113 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1968676649/5000000000 : ℝ)^9 ≤ (30168137297207/100000000000000 : ℝ)^7 := by
    have hnat : (1968676649 : ℕ)^9*100000000000000^7 ≤ 30168137297207^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1968676649 5000000000 30168137297207 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6303681659/10000000000 : ℝ)^9 ≤ (55250408531171/100000000000000 : ℝ)^7 := by
    have hnat : (6303681659 : ℕ)^9*100000000000000^7 ≤ 55250408531171^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6303681659 10000000000 55250408531171 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-69899311/312500000 : ℝ), (1968676649/5000000000 : ℝ), (6303681659/10000000000 : ℝ)] ![(14581454164113/100000000000000 : ℝ), (30168137297207/100000000000000 : ℝ), (55250408531171/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-69899311/312500000 : ℝ)|^9 ≤ (14581454164113/100000000000000 : ℝ)^7
        have hw : |(-69899311/312500000 : ℝ)|=(69899311/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1968676649/5000000000 : ℝ)|^9 ≤ (30168137297207/100000000000000 : ℝ)^7
        have hw : |(1968676649/5000000000 : ℝ)|=(1968676649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6303681659/10000000000 : ℝ)|^9 ≤ (55250408531171/100000000000000 : ℝ)^7
        have hw : |(6303681659/10000000000 : ℝ)|=(6303681659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s3_s3_8 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2177437761/5000000000 : ℝ)*x 0 + (-453784447/2500000000 : ℝ)*x 1 + (6237940343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177437761/5000000000 : ℝ)^9 ≤ (17171014827869/50000000000000 : ℝ)^7 := by
    have hnat : (2177437761 : ℕ)^9*50000000000000^7 ≤ 17171014827869^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177437761 5000000000 17171014827869 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (453784447/2500000000 : ℝ)^9 ≤ (696705919757/6250000000000 : ℝ)^7 := by
    have hnat : (453784447 : ℕ)^9*6250000000000^7 ≤ 696705919757^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453784447 2500000000 696705919757 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6237940343/10000000000 : ℝ)^9 ≤ (54510675611709/100000000000000 : ℝ)^7 := by
    have hnat : (6237940343 : ℕ)^9*100000000000000^7 ≤ 54510675611709^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6237940343 10000000000 54510675611709 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177437761/5000000000 : ℝ), (-453784447/2500000000 : ℝ), (6237940343/10000000000 : ℝ)] ![(17171014827869/50000000000000 : ℝ), (696705919757/6250000000000 : ℝ), (54510675611709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177437761/5000000000 : ℝ)|^9 ≤ (17171014827869/50000000000000 : ℝ)^7
        have hw : |(2177437761/5000000000 : ℝ)|=(2177437761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-453784447/2500000000 : ℝ)|^9 ≤ (696705919757/6250000000000 : ℝ)^7
        have hw : |(-453784447/2500000000 : ℝ)|=(453784447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6237940343/10000000000 : ℝ)|^9 ≤ (54510675611709/100000000000000 : ℝ)^7
        have hw : |(6237940343/10000000000 : ℝ)|=(6237940343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s3_s3_9 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (442330423/1000000000 : ℝ)*x 0 + (685002251/1000000000 : ℝ)*x 1 + (-734088693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (442330423/1000000000 : ℝ)^9 ≤ (35037379225443/100000000000000 : ℝ)^7 := by
    have hnat : (442330423 : ℕ)^9*100000000000000^7 ≤ 35037379225443^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442330423 1000000000 35037379225443 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (685002251/1000000000 : ℝ)^9 ≤ (30740919929689/50000000000000 : ℝ)^7 := by
    have hnat : (685002251 : ℕ)^9*50000000000000^7 ≤ 30740919929689^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      685002251 1000000000 30740919929689 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (734088693/10000000000 : ℝ)^9 ≤ (1740390451531/50000000000000 : ℝ)^7 := by
    have hnat : (734088693 : ℕ)^9*50000000000000^7 ≤ 1740390451531^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      734088693 10000000000 1740390451531 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(442330423/1000000000 : ℝ), (685002251/1000000000 : ℝ), (-734088693/10000000000 : ℝ)] ![(35037379225443/100000000000000 : ℝ), (30740919929689/50000000000000 : ℝ), (1740390451531/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(442330423/1000000000 : ℝ)|^9 ≤ (35037379225443/100000000000000 : ℝ)^7
        have hw : |(442330423/1000000000 : ℝ)|=(442330423/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(685002251/1000000000 : ℝ)|^9 ≤ (30740919929689/50000000000000 : ℝ)^7
        have hw : |(685002251/1000000000 : ℝ)|=(685002251/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-734088693/10000000000 : ℝ)|^9 ≤ (1740390451531/50000000000000 : ℝ)^7
        have hw : |(-734088693/10000000000 : ℝ)|=(734088693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s3_s3_13 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (239949167/400000000 : ℝ)*x 0 + (4048157819/10000000000 : ℝ)*x 1 + (1254289823/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (239949167/400000000 : ℝ)^9 ≤ (51837925584751/100000000000000 : ℝ)^7 := by
    have hnat : (239949167 : ℕ)^9*100000000000000^7 ≤ 51837925584751^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      239949167 400000000 51837925584751 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4048157819/10000000000 : ℝ)^9 ≤ (7816013172359/25000000000000 : ℝ)^7 := by
    have hnat : (4048157819 : ℕ)^9*25000000000000^7 ≤ 7816013172359^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4048157819 10000000000 7816013172359 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1254289823/5000000000 : ℝ)^9 ≤ (135184173747/800000000000 : ℝ)^7 := by
    have hnat : (1254289823 : ℕ)^9*800000000000^7 ≤ 135184173747^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1254289823 5000000000 135184173747 800000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(239949167/400000000 : ℝ), (4048157819/10000000000 : ℝ), (1254289823/5000000000 : ℝ)] ![(51837925584751/100000000000000 : ℝ), (7816013172359/25000000000000 : ℝ), (135184173747/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(239949167/400000000 : ℝ)|^9 ≤ (51837925584751/100000000000000 : ℝ)^7
        have hw : |(239949167/400000000 : ℝ)|=(239949167/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4048157819/10000000000 : ℝ)|^9 ≤ (7816013172359/25000000000000 : ℝ)^7
        have hw : |(4048157819/10000000000 : ℝ)|=(4048157819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1254289823/5000000000 : ℝ)|^9 ≤ (135184173747/800000000000 : ℝ)^7
        have hw : |(1254289823/5000000000 : ℝ)|=(1254289823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s3_s3_14 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-55979631/400000000 : ℝ)*x 0 + (4596089257/10000000000 : ℝ)*x 1 + (6300447461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (55979631/400000000 : ℝ)^9 ≤ (3989619559979/50000000000000 : ℝ)^7 := by
    have hnat : (55979631 : ℕ)^9*50000000000000^7 ≤ 3989619559979^7*400000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55979631 400000000 3989619559979 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4596089257/10000000000 : ℝ)^9 ≤ (4600849483/12500000000 : ℝ)^7 := by
    have hnat : (4596089257 : ℕ)^9*12500000000^7 ≤ 4600849483^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4596089257 10000000000 4600849483 12500000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6300447461/10000000000 : ℝ)^9 ≤ (6901745624929/12500000000000 : ℝ)^7 := by
    have hnat : (6300447461 : ℕ)^9*12500000000000^7 ≤ 6901745624929^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6300447461 10000000000 6901745624929 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-55979631/400000000 : ℝ), (4596089257/10000000000 : ℝ), (6300447461/10000000000 : ℝ)] ![(3989619559979/50000000000000 : ℝ), (4600849483/12500000000 : ℝ), (6901745624929/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-55979631/400000000 : ℝ)|^9 ≤ (3989619559979/50000000000000 : ℝ)^7
        have hw : |(-55979631/400000000 : ℝ)|=(55979631/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4596089257/10000000000 : ℝ)|^9 ≤ (4600849483/12500000000 : ℝ)^7
        have hw : |(4596089257/10000000000 : ℝ)|=(4596089257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6300447461/10000000000 : ℝ)|^9 ≤ (6901745624929/12500000000000 : ℝ)^7
        have hw : |(6300447461/10000000000 : ℝ)|=(6300447461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s3_s3_15 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4227072291/10000000000 : ℝ)*x 0 + (-1981033849/10000000000 : ℝ)*x 1 + (1558676707/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4227072291/10000000000 : ℝ)^9 ≤ (6610341003241/20000000000000 : ℝ)^7 := by
    have hnat : (4227072291 : ℕ)^9*20000000000000^7 ≤ 6610341003241^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4227072291 10000000000 6610341003241 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1981033849/10000000000 : ℝ)^9 ≤ (779621637351/6250000000000 : ℝ)^7 := by
    have hnat : (1981033849 : ℕ)^9*6250000000000^7 ≤ 779621637351^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1981033849 10000000000 779621637351 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1558676707/2500000000 : ℝ)^9 ≤ (54474348779191/100000000000000 : ℝ)^7 := by
    have hnat : (1558676707 : ℕ)^9*100000000000000^7 ≤ 54474348779191^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1558676707 2500000000 54474348779191 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4227072291/10000000000 : ℝ), (-1981033849/10000000000 : ℝ), (1558676707/2500000000 : ℝ)] ![(6610341003241/20000000000000 : ℝ), (779621637351/6250000000000 : ℝ), (54474348779191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4227072291/10000000000 : ℝ)|^9 ≤ (6610341003241/20000000000000 : ℝ)^7
        have hw : |(4227072291/10000000000 : ℝ)|=(4227072291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1981033849/10000000000 : ℝ)|^9 ≤ (779621637351/6250000000000 : ℝ)^7
        have hw : |(-1981033849/10000000000 : ℝ)|=(1981033849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1558676707/2500000000 : ℝ)|^9 ≤ (54474348779191/100000000000000 : ℝ)^7
        have hw : |(1558676707/2500000000 : ℝ)|=(1558676707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s3_s3_16 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (703489383/1250000000 : ℝ)*x 0 + (357401107/625000000 : ℝ)*x 1 + (-737322547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (703489383/1250000000 : ℝ)^9 ≤ (47754935037197/100000000000000 : ℝ)^7 := by
    have hnat : (703489383 : ℕ)^9*100000000000000^7 ≤ 47754935037197^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      703489383 1250000000 47754935037197 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (357401107/625000000 : ℝ)^9 ≤ (24372278415061/50000000000000 : ℝ)^7 := by
    have hnat : (357401107 : ℕ)^9*50000000000000^7 ≤ 24372278415061^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357401107 625000000 24372278415061 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (737322547/10000000000 : ℝ)^9 ≤ (3500508126823/100000000000000 : ℝ)^7 := by
    have hnat : (737322547 : ℕ)^9*100000000000000^7 ≤ 3500508126823^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      737322547 10000000000 3500508126823 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(703489383/1250000000 : ℝ), (357401107/625000000 : ℝ), (-737322547/10000000000 : ℝ)] ![(47754935037197/100000000000000 : ℝ), (24372278415061/50000000000000 : ℝ), (3500508126823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(703489383/1250000000 : ℝ)|^9 ≤ (47754935037197/100000000000000 : ℝ)^7
        have hw : |(703489383/1250000000 : ℝ)|=(703489383/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(357401107/625000000 : ℝ)|^9 ≤ (24372278415061/50000000000000 : ℝ)^7
        have hw : |(357401107/625000000 : ℝ)|=(357401107/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-737322547/10000000000 : ℝ)|^9 ≤ (3500508126823/100000000000000 : ℝ)^7
        have hw : |(-737322547/10000000000 : ℝ)|=(737322547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s3_s3_20 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3565529307/5000000000 : ℝ)*x 0 + (2668346419/10000000000 : ℝ)*x 1 + (628994141/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3565529307/5000000000 : ℝ)^9 ≤ (161859433703/250000000000 : ℝ)^7 := by
    have hnat : (3565529307 : ℕ)^9*250000000000^7 ≤ 161859433703^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3565529307 5000000000 161859433703 250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2668346419/10000000000 : ℝ)^9 ≤ (18294115411429/100000000000000 : ℝ)^7 := by
    have hnat : (2668346419 : ℕ)^9*100000000000000^7 ≤ 18294115411429^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2668346419 10000000000 18294115411429 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (628994141/2500000000 : ℝ)^9 ≤ (4240527772627/25000000000000 : ℝ)^7 := by
    have hnat : (628994141 : ℕ)^9*25000000000000^7 ≤ 4240527772627^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      628994141 2500000000 4240527772627 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3565529307/5000000000 : ℝ), (2668346419/10000000000 : ℝ), (628994141/2500000000 : ℝ)] ![(161859433703/250000000000 : ℝ), (18294115411429/100000000000000 : ℝ), (4240527772627/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3565529307/5000000000 : ℝ)|^9 ≤ (161859433703/250000000000 : ℝ)^7
        have hw : |(3565529307/5000000000 : ℝ)|=(3565529307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2668346419/10000000000 : ℝ)|^9 ≤ (18294115411429/100000000000000 : ℝ)^7
        have hw : |(2668346419/10000000000 : ℝ)|=(2668346419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(628994141/2500000000 : ℝ)|^9 ≤ (4240527772627/25000000000000 : ℝ)^7
        have hw : |(628994141/2500000000 : ℝ)|=(628994141/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s3_s3_21 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-172048749/1250000000 : ℝ)*x 0 + (1278620997/2500000000 : ℝ)*x 1 + (182161059/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172048749/1250000000 : ℝ)^9 ≤ (244071838427/3125000000000 : ℝ)^7 := by
    have hnat : (172048749 : ℕ)^9*3125000000000^7 ≤ 244071838427^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172048749 1250000000 244071838427 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1278620997/2500000000 : ℝ)^9 ≤ (21114089034629/50000000000000 : ℝ)^7 := by
    have hnat : (1278620997 : ℕ)^9*50000000000000^7 ≤ 21114089034629^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1278620997 2500000000 21114089034629 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (182161059/312500000 : ℝ)^9 ≤ (9992304618341/20000000000000 : ℝ)^7 := by
    have hnat : (182161059 : ℕ)^9*20000000000000^7 ≤ 9992304618341^7*312500000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182161059 312500000 9992304618341 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-172048749/1250000000 : ℝ), (1278620997/2500000000 : ℝ), (182161059/312500000 : ℝ)] ![(244071838427/3125000000000 : ℝ), (21114089034629/50000000000000 : ℝ), (9992304618341/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-172048749/1250000000 : ℝ)|^9 ≤ (244071838427/3125000000000 : ℝ)^7
        have hw : |(-172048749/1250000000 : ℝ)|=(172048749/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1278620997/2500000000 : ℝ)|^9 ≤ (21114089034629/50000000000000 : ℝ)^7
        have hw : |(1278620997/2500000000 : ℝ)|=(1278620997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(182161059/312500000 : ℝ)|^9 ≤ (9992304618341/20000000000000 : ℝ)^7
        have hw : |(182161059/312500000 : ℝ)|=(182161059/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s3_s3_22 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5582585899/10000000000 : ℝ)*x 0 + (-29250231/200000000 : ℝ)*x 1 + (663516251/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5582585899/10000000000 : ℝ)^9 ≤ (47260974841481/100000000000000 : ℝ)^7 := by
    have hnat : (5582585899 : ℕ)^9*100000000000000^7 ≤ 47260974841481^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5582585899 10000000000 47260974841481 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (29250231/200000000 : ℝ)^9 ≤ (8444156013781/100000000000000 : ℝ)^7 := by
    have hnat : (29250231 : ℕ)^9*100000000000000^7 ≤ 8444156013781^7*200000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29250231 200000000 8444156013781 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (663516251/1250000000 : ℝ)^9 ≤ (8858973826783/20000000000000 : ℝ)^7 := by
    have hnat : (663516251 : ℕ)^9*20000000000000^7 ≤ 8858973826783^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663516251 1250000000 8858973826783 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5582585899/10000000000 : ℝ), (-29250231/200000000 : ℝ), (663516251/1250000000 : ℝ)] ![(47260974841481/100000000000000 : ℝ), (8444156013781/100000000000000 : ℝ), (8858973826783/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5582585899/10000000000 : ℝ)|^9 ≤ (47260974841481/100000000000000 : ℝ)^7
        have hw : |(5582585899/10000000000 : ℝ)|=(5582585899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-29250231/200000000 : ℝ)|^9 ≤ (8444156013781/100000000000000 : ℝ)^7
        have hw : |(-29250231/200000000 : ℝ)|=(29250231/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(663516251/1250000000 : ℝ)|^9 ≤ (8858973826783/20000000000000 : ℝ)^7
        have hw : |(663516251/1250000000 : ℝ)|=(663516251/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s3_s3_23 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4203038491/10000000000 : ℝ)*x 0 + (1692803931/2500000000 : ℝ)*x 1 + (-1209691601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4203038491/10000000000 : ℝ)^9 ≤ (32810288081643/100000000000000 : ℝ)^7 := by
    have hnat : (4203038491 : ℕ)^9*100000000000000^7 ≤ 32810288081643^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4203038491 10000000000 32810288081643 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1692803931/2500000000 : ℝ)^9 ≤ (30286960938943/50000000000000 : ℝ)^7 := by
    have hnat : (1692803931 : ℕ)^9*50000000000000^7 ≤ 30286960938943^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1692803931 2500000000 30286960938943 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1209691601/10000000000 : ℝ)^9 ≤ (826973752401/12500000000000 : ℝ)^7 := by
    have hnat : (1209691601 : ℕ)^9*12500000000000^7 ≤ 826973752401^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1209691601 10000000000 826973752401 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4203038491/10000000000 : ℝ), (1692803931/2500000000 : ℝ), (-1209691601/10000000000 : ℝ)] ![(32810288081643/100000000000000 : ℝ), (30286960938943/50000000000000 : ℝ), (826973752401/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4203038491/10000000000 : ℝ)|^9 ≤ (32810288081643/100000000000000 : ℝ)^7
        have hw : |(4203038491/10000000000 : ℝ)|=(4203038491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1692803931/2500000000 : ℝ)|^9 ≤ (30286960938943/50000000000000 : ℝ)^7
        have hw : |(1692803931/2500000000 : ℝ)|=(1692803931/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1209691601/10000000000 : ℝ)|^9 ≤ (826973752401/12500000000000 : ℝ)^7
        have hw : |(-1209691601/10000000000 : ℝ)|=(1209691601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s3_s3_27 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (73425231/100000000 : ℝ)*x 0 + (2342775747/10000000000 : ℝ)*x 1 + (2555051371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (73425231/100000000 : ℝ)^9 ≤ (67222616640029/100000000000000 : ℝ)^7 := by
    have hnat : (73425231 : ℕ)^9*100000000000000^7 ≤ 67222616640029^7*100000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73425231 100000000 67222616640029 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2342775747/10000000000 : ℝ)^9 ≤ (15475824004473/100000000000000 : ℝ)^7 := by
    have hnat : (2342775747 : ℕ)^9*100000000000000^7 ≤ 15475824004473^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2342775747 10000000000 15475824004473 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2555051371/10000000000 : ℝ)^9 ≤ (3460311868859/20000000000000 : ℝ)^7 := by
    have hnat : (2555051371 : ℕ)^9*20000000000000^7 ≤ 3460311868859^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2555051371 10000000000 3460311868859 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(73425231/100000000 : ℝ), (2342775747/10000000000 : ℝ), (2555051371/10000000000 : ℝ)] ![(67222616640029/100000000000000 : ℝ), (15475824004473/100000000000000 : ℝ), (3460311868859/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(73425231/100000000 : ℝ)|^9 ≤ (67222616640029/100000000000000 : ℝ)^7
        have hw : |(73425231/100000000 : ℝ)|=(73425231/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2342775747/10000000000 : ℝ)|^9 ≤ (15475824004473/100000000000000 : ℝ)^7
        have hw : |(2342775747/10000000000 : ℝ)|=(2342775747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2555051371/10000000000 : ℝ)|^9 ≤ (3460311868859/20000000000000 : ℝ)^7
        have hw : |(2555051371/10000000000 : ℝ)|=(2555051371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c311061_s3 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((50713/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(50713/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(56997/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(56997/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(25593/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(25593/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((14351/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14351/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34161/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(34161/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31369/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(31369/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (19517/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19517/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19517/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19517/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (50713/100000 : ℝ) ^ (71/16 : ℝ) ≤ (982871859562541821/20000000000000000000 : ℝ) := by
    have hpowers : (50713/100000 : ℝ)^71 ≤ (982871859562541821/20000000000000000000 : ℝ)^16 := by
      have hnat : (50713 : ℕ)^71*20000000000000000000^16 ≤ 982871859562541821^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50713 100000 982871859562541821 20000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (50713/100000 : ℝ)) (X := (982871859562541821/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s3_corner0a : (20982871859562541821/20000000000000000000 : ℝ) ≤ (5054348697904471/5000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (20982871859562541821/20000000000000000000 : ℝ)^16 ≤ (5054348697904471/5000000000000000 : ℝ)^71 := by
      have hnat : (20982871859562541821 : ℕ)^16*5000000000000000^71 ≤ 5054348697904471^71*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20982871859562541821 20000000000000000000 5054348697904471 5000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5054348697904471/5000000000000000 : ℝ)) (X := (20982871859562541821/20000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s3_corner0b : (10982871859562541821/10000000000000000000 : ℝ) ≤ (1021351939224073/1000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (10982871859562541821/10000000000000000000 : ℝ)^16 ≤ (1021351939224073/1000000000000000 : ℝ)^71 := by
      have hnat : (10982871859562541821 : ℕ)^16*1000000000000000^71 ≤ 1021351939224073^71*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10982871859562541821 10000000000000000000 1021351939224073 1000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1021351939224073/1000000000000000 : ℝ)) (X := (10982871859562541821/10000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(54348697904471/2535650000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(26205499107947/1267825000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (50713/100000 : ℝ)) (alpha := (54348697904471/2535650000000000 : ℝ)) (beta := (26205499107947/1267825000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (50713/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(54348697904471/2535650000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(26205499107947/1267825000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (56997/100000 : ℝ) ^ (71/16 : ℝ) ≤ (4126323213357791359/50000000000000000000 : ℝ) := by
    have hpowers : (56997/100000 : ℝ)^71 ≤ (4126323213357791359/50000000000000000000 : ℝ)^16 := by
      have hnat : (56997 : ℕ)^71*50000000000000000000^16 ≤ 4126323213357791359^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56997 100000 4126323213357791359 50000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (56997/100000 : ℝ)) (X := (4126323213357791359/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s3_corner1a : (54126323213357791359/50000000000000000000 : ℝ) ≤ (509015254888183/500000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (54126323213357791359/50000000000000000000 : ℝ)^16 ≤ (509015254888183/500000000000000 : ℝ)^71 := by
      have hnat : (54126323213357791359 : ℕ)^16*500000000000000^71 ≤ 509015254888183^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54126323213357791359 50000000000000000000 509015254888183 500000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (509015254888183/500000000000000 : ℝ)) (X := (54126323213357791359/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s3_corner1b : (29126323213357791359/25000000000000000000 : ℝ) ≤ (646891062691803/625000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (29126323213357791359/25000000000000000000 : ℝ)^16 ≤ (646891062691803/625000000000000 : ℝ)^71 := by
      have hnat : (29126323213357791359 : ℕ)^16*625000000000000^71 ≤ 646891062691803^71*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29126323213357791359 25000000000000000000 646891062691803 625000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (646891062691803/625000000000000 : ℝ)) (X := (29126323213357791359/25000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(9015254888183/284985000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(42487976326297/1424925000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (56997/100000 : ℝ)) (alpha := (9015254888183/284985000000000 : ℝ)) (beta := (42487976326297/1424925000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (56997/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(9015254888183/284985000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(42487976326297/1424925000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (25593/50000 : ℝ) ^ (71/16 : ℝ) ≤ (20004073919626459/390625000000000000 : ℝ) := by
    have hpowers : (25593/50000 : ℝ)^71 ≤ (20004073919626459/390625000000000000 : ℝ)^16 := by
      have hnat : (25593 : ℕ)^71*390625000000000000^16 ≤ 20004073919626459^16*50000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25593 50000 20004073919626459 390625000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (25593/50000 : ℝ)) (X := (20004073919626459/390625000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s3_corner2a : (410629073919626459/390625000000000000 : ℝ) ≤ (2022636343676307/2000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (410629073919626459/390625000000000000 : ℝ)^16 ≤ (2022636343676307/2000000000000000 : ℝ)^71 := by
      have hnat : (410629073919626459 : ℕ)^16*2000000000000000^71 ≤ 2022636343676307^71*390625000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        410629073919626459 390625000000000000 2022636343676307 2000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2022636343676307/2000000000000000 : ℝ)) (X := (410629073919626459/390625000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s3_corner2b : (215316573919626459/195312500000000000 : ℝ) ≤ (10222169570128763/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (215316573919626459/195312500000000000 : ℝ)^16 ≤ (10222169570128763/10000000000000000 : ℝ)^71 := by
      have hnat : (215316573919626459 : ℕ)^16*10000000000000000^71 ≤ 10222169570128763^71*195312500000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        215316573919626459 195312500000000000 10222169570128763 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10222169570128763/10000000000000000 : ℝ)) (X := (215316573919626459/195312500000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(22636343676307/1023720000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(27246962936807/1279650000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (25593/50000 : ℝ)) (alpha := (22636343676307/1023720000000000 : ℝ)) (beta := (27246962936807/1279650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (25593/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(22636343676307/1023720000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(27246962936807/1279650000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-2230947287/10000000000 : ℝ)*X 0 0+(1126202113/2500000000 : ℝ)*X 0 1+(5796119303/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((4687931263/10000000000 : ℝ)*X 1 0+(-2315116183/10000000000 : ℝ)*X 1 1+(5558923271/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((1188991811/2500000000 : ℝ)*X 2 0+(77130919/125000000 : ℝ)*X 2 1+(-85808329/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((1503739991/2500000000 : ℝ)*X 0 0+(2988907241/10000000000 : ℝ)*X 0 1+(898133981/2500000000 : ℝ)*X 0 2+(1503739991/2500000000 : ℝ)*X 1 0+(2988907241/10000000000 : ℝ)*X 1 1+(898133981/2500000000 : ℝ)*X 1 2+(1503739991/2500000000 : ℝ)*X 2 0+(2988907241/10000000000 : ℝ)*X 2 1+(898133981/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-69899311/312500000 : ℝ)*X 0 0+(1968676649/5000000000 : ℝ)*X 0 1+(6303681659/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((2177437761/5000000000 : ℝ)*X 1 0+(-453784447/2500000000 : ℝ)*X 1 1+(6237940343/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((442330423/1000000000 : ℝ)*X 2 0+(685002251/1000000000 : ℝ)*X 2 1+(-734088693/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((239949167/400000000 : ℝ)*X 0 0+(4048157819/10000000000 : ℝ)*X 0 1+(1254289823/5000000000 : ℝ)*X 0 2+(239949167/400000000 : ℝ)*X 1 0+(4048157819/10000000000 : ℝ)*X 1 1+(1254289823/5000000000 : ℝ)*X 1 2+(239949167/400000000 : ℝ)*X 2 0+(4048157819/10000000000 : ℝ)*X 2 1+(1254289823/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-55979631/400000000 : ℝ)*X 0 0+(4596089257/10000000000 : ℝ)*X 0 1+(6300447461/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((4227072291/10000000000 : ℝ)*X 1 0+(-1981033849/10000000000 : ℝ)*X 1 1+(1558676707/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((703489383/1250000000 : ℝ)*X 2 0+(357401107/625000000 : ℝ)*X 2 1+(-737322547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((3565529307/5000000000 : ℝ)*X 0 0+(2668346419/10000000000 : ℝ)*X 0 1+(628994141/2500000000 : ℝ)*X 0 2+(3565529307/5000000000 : ℝ)*X 1 0+(2668346419/10000000000 : ℝ)*X 1 1+(628994141/2500000000 : ℝ)*X 1 2+(3565529307/5000000000 : ℝ)*X 2 0+(2668346419/10000000000 : ℝ)*X 2 1+(628994141/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-172048749/1250000000 : ℝ)*X 0 0+(1278620997/2500000000 : ℝ)*X 0 1+(182161059/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((5582585899/10000000000 : ℝ)*X 1 0+(-29250231/200000000 : ℝ)*X 1 1+(663516251/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((4203038491/10000000000 : ℝ)*X 2 0+(1692803931/2500000000 : ℝ)*X 2 1+(-1209691601/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((73425231/100000000 : ℝ)*X 0 0+(2342775747/10000000000 : ℝ)*X 0 1+(2555051371/10000000000 : ℝ)*X 0 2+(73425231/100000000 : ℝ)*X 1 0+(2342775747/10000000000 : ℝ)*X 1 1+(2555051371/10000000000 : ℝ)*X 1 2+(73425231/100000000 : ℝ)*X 2 0+(2342775747/10000000000 : ℝ)*X 2 1+(2555051371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((14351/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14351/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (142256944755826949816248191353/45664371246650000000000000000000000 : ℝ) := by norm_num
    linear_combination (238299/1000000000000 : ℝ)*(base50) + (1035985073779/1000000000000 : ℝ)*(base59) + (252687/250000000000 : ℝ)*(base60) + (5615244700391/1000000000000 : ℝ)*(major_s3_0) + (5615244700391/1000000000000 : ℝ)*(major_s3_1) + (5615244700391/1000000000000 : ℝ)*(major_s3_2) + (15114199/1000000000000 : ℝ)*(sp_s3_0) + (1208251/100000000000 : ℝ)*(sp_s3_6) + (3906896790189/500000000000 : ℝ)*(sp_s3_7) + (1953434980921/250000000000 : ℝ)*(sp_s3_8) + (62510266397/8000000000 : ℝ)*(sp_s3_9) + (3416667585263/1000000000000 : ℝ)*(sp_s3_13) + (68770893/1000000000000 : ℝ)*(sp_s3_15) + (3174369/125000000000 : ℝ)*(sp_s3_23) + (854169916943/250000000000 : ℝ)*(f.failure) + (7813808694577/1000000000000 : ℝ)*(f.sum) + (8218757914741820981/19449656280000000000000000000000 : ℝ)*base62 + (23904698339009/159956250000000000000000000 : ℝ)*base64 + (1407470615167309/2849850000000000000000000000 : ℝ)*base67 + (46310496963553/204744000000000000000000000 : ℝ)*base69 + (18597562508922430259/32447445225000000000000000000000 : ℝ)*base70 + (44958859469409/158478125000000000000000000 : ℝ)*base73 + (82364204153353/569970000000000000000000000 : ℝ)*base74 + (151141977527709/633912500000000000000000000 : ℝ)*base77 + (1311304329984693167/28904888610000000000000000000000 : ℝ)*base79 + (6709/6250000000000000 : ℝ)*base86 + (6709/6250000000000000 : ℝ)*base88 + (6709/6250000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34161/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(34161/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1197150799430619674121671829413/102744835304962500000000000000000000 : ℝ) := by norm_num
    linear_combination (5541/6250000000 : ℝ)*(base39) + (172363/200000000000 : ℝ)*(base49) + (152973036099/250000000000 : ℝ)*(base59) + (1348367946173/250000000000 : ℝ)*(major_s3_0) + (1348367946173/250000000000 : ℝ)*(major_s3_1) + (1348367946173/250000000000 : ℝ)*(major_s3_2) + (28414667/1000000000000 : ℝ)*(sp_s3_2) + (23108793/1000000000000 : ℝ)*(sp_s3_6) + (1564569/25000000000 : ℝ)*(sp_s3_7) + (7505138484247/1000000000000 : ℝ)*(sp_s3_14) + (7505201067007/1000000000000 : ℝ)*(sp_s3_15) + (375258632617/50000000000 : ℝ)*(sp_s3_16) + (1640758097813/500000000000 : ℝ)*(sp_s3_20) + (199314057/1000000000000 : ℝ)*(sp_s3_27) + (820434654619/250000000000 : ℝ)*(f.failure) + (7505201067007/1000000000000 : ℝ)*(f.sum) + (249243102934572269/1215603517500000000000000000000 : ℝ)*base62 + (763882685410369/1279650000000000000000000000 : ℝ)*base64 + (363695150304601/1424925000000000000000000000 : ℝ)*base66 + (78180183847409/127965000000000000000000000 : ℝ)*base68 + (13715615553200650831/64894890450000000000000000000000 : ℝ)*base70 + (2105494461799887/2535650000000000000000000000 : ℝ)*base72 + (1352458586401/2226445312500000000000000 : ℝ)*base74 + (676348688375979/1267825000000000000000000000 : ℝ)*base76 + (2880882161031196519/28904888610000000000000000000000 : ℝ)*base78 + (5853/6250000000000000 : ℝ)*base87 + (5853/6250000000000000 : ℝ)*base89 + (5853/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31369/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(31369/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (9301454998204415056089487219/990311665590000000000000000000000 : ℝ) := by norm_num
    linear_combination (980463/200000000000 : ℝ)*(base15) + (157215894083/500000000000 : ℝ)*(base40) + (617684385267/1000000000000 : ℝ)*(base59) + (496303466969/100000000000 : ℝ)*(major_s3_0) + (496303466969/100000000000 : ℝ)*(major_s3_1) + (496303466969/100000000000 : ℝ)*(major_s3_2) + (659233/1000000000000 : ℝ)*(sp_s3_1) + (155396751/1000000000000 : ℝ)*(sp_s3_2) + (6919329/250000000000 : ℝ)*(sp_s3_9) + (419654381/1000000000000 : ℝ)*(sp_s3_20) + (345311674701/50000000000 : ℝ)*(sp_s3_21) + (863278491559/125000000000 : ℝ)*(sp_s3_22) + (6906050419953/1000000000000 : ℝ)*(sp_s3_23) + (1509706530079/500000000000 : ℝ)*(sp_s3_27) + (3019832714539/1000000000000 : ℝ)*(f.failure) + (345311674701/50000000000 : ℝ)*(f.sum) + (1695020766416548651/9724828140000000000000000000000 : ℝ)*base62 + (108065494075991/255930000000000000000000000 : ℝ)*base64 + (74843676219521/284985000000000000000000000 : ℝ)*base66 + (274089507123011/511860000000000000000000000 : ℝ)*base68 + (39492092009616983/78186615000000000000000000000 : ℝ)*base70 + (745599658053/6110000000000000000000000 : ℝ)*base73 + (218788051111717/569970000000000000000000000 : ℝ)*base74 + (2813819704581/6110000000000000000000000 : ℝ)*base76 + (60149126476977241/348251670000000000000000000000 : ℝ)*base79 + (13893/25000000000000000 : ℝ)*base87 + (13893/25000000000000000 : ℝ)*base89 + (13893/25000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((50713/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(50713/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(56997/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(56997/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(25593/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(25593/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((14351/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14351/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34161/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(34161/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31369/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(31369/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c311061_s3 p hpa hpb X hX hprev2

#print axioms solution
