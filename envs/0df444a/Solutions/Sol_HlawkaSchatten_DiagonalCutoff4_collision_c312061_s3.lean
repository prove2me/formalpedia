-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c312061_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:20:51.464285+00:00
-- url     : https://prove2.me/submissions/5895d918-a454-4d87-bc34-977e4f27408d

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
theorem collision_support_c312061_s3_s3_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2305791233/10000000000 : ℝ)*x 0 + (4489485801/10000000000 : ℝ)*x 1 + (5717310777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2305791233/10000000000 : ℝ)^73 ≤ (15274339351117/100000000000000 : ℝ)^57 := by
    have hnat : (2305791233 : ℕ)^73*100000000000000^57 ≤ 15274339351117^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2305791233 10000000000 15274339351117 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4489485801/10000000000 : ℝ)^73 ≤ (35856473844229/100000000000000 : ℝ)^57 := by
    have hnat : (4489485801 : ℕ)^73*100000000000000^57 ≤ 35856473844229^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489485801 10000000000 35856473844229 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5717310777/10000000000 : ℝ)^73 ≤ (12217296695983/25000000000000 : ℝ)^57 := by
    have hnat : (5717310777 : ℕ)^73*25000000000000^57 ≤ 12217296695983^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5717310777 10000000000 12217296695983 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2305791233/10000000000 : ℝ), (4489485801/10000000000 : ℝ), (5717310777/10000000000 : ℝ)] ![(15274339351117/100000000000000 : ℝ), (35856473844229/100000000000000 : ℝ), (12217296695983/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2305791233/10000000000 : ℝ)|^73 ≤ (15274339351117/100000000000000 : ℝ)^57
        have hw : |(-2305791233/10000000000 : ℝ)|=(2305791233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4489485801/10000000000 : ℝ)|^73 ≤ (35856473844229/100000000000000 : ℝ)^57
        have hw : |(4489485801/10000000000 : ℝ)|=(4489485801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5717310777/10000000000 : ℝ)|^73 ≤ (12217296695983/25000000000000 : ℝ)^57
        have hw : |(5717310777/10000000000 : ℝ)|=(5717310777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s3_s3_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1168679957/2500000000 : ℝ)*x 0 + (-23691619/100000000 : ℝ)*x 1 + (1098537393/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1168679957/2500000000 : ℝ)^73 ≤ (37762035935387/100000000000000 : ℝ)^57 := by
    have hnat : (1168679957 : ℕ)^73*100000000000000^57 ≤ 37762035935387^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1168679957 2500000000 37762035935387 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (23691619/100000000 : ℝ)^73 ≤ (7907011864737/50000000000000 : ℝ)^57 := by
    have hnat : (23691619 : ℕ)^73*50000000000000^57 ≤ 7907011864737^57*100000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23691619 100000000 7907011864737 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1098537393/2000000000 : ℝ)^73 ≤ (46423940322403/100000000000000 : ℝ)^57 := by
    have hnat : (1098537393 : ℕ)^73*100000000000000^57 ≤ 46423940322403^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098537393 2000000000 46423940322403 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1168679957/2500000000 : ℝ), (-23691619/100000000 : ℝ), (1098537393/2000000000 : ℝ)] ![(37762035935387/100000000000000 : ℝ), (7907011864737/50000000000000 : ℝ), (46423940322403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1168679957/2500000000 : ℝ)|^73 ≤ (37762035935387/100000000000000 : ℝ)^57
        have hw : |(1168679957/2500000000 : ℝ)|=(1168679957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-23691619/100000000 : ℝ)|^73 ≤ (7907011864737/50000000000000 : ℝ)^57
        have hw : |(-23691619/100000000 : ℝ)|=(23691619/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1098537393/2000000000 : ℝ)|^73 ≤ (46423940322403/100000000000000 : ℝ)^57
        have hw : |(1098537393/2000000000 : ℝ)|=(1098537393/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s3_s3_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (943204901/2000000000 : ℝ)*x 0 + (3048371641/5000000000 : ℝ)*x 1 + (-1492337263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (943204901/2000000000 : ℝ)^73 ≤ (38189878659709/100000000000000 : ℝ)^57 := by
    have hnat : (943204901 : ℕ)^73*100000000000000^57 ≤ 38189878659709^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943204901 2000000000 38189878659709 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3048371641/5000000000 : ℝ)^73 ≤ (26530444025851/50000000000000 : ℝ)^57 := by
    have hnat : (3048371641 : ℕ)^73*50000000000000^57 ≤ 26530444025851^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3048371641 5000000000 26530444025851 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1492337263/10000000000 : ℝ)^73 ≤ (4374616638681/50000000000000 : ℝ)^57 := by
    have hnat : (1492337263 : ℕ)^73*50000000000000^57 ≤ 4374616638681^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1492337263 10000000000 4374616638681 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(943204901/2000000000 : ℝ), (3048371641/5000000000 : ℝ), (-1492337263/10000000000 : ℝ)] ![(38189878659709/100000000000000 : ℝ), (26530444025851/50000000000000 : ℝ), (4374616638681/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(943204901/2000000000 : ℝ)|^73 ≤ (38189878659709/100000000000000 : ℝ)^57
        have hw : |(943204901/2000000000 : ℝ)|=(943204901/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3048371641/5000000000 : ℝ)|^73 ≤ (26530444025851/50000000000000 : ℝ)^57
        have hw : |(3048371641/5000000000 : ℝ)|=(3048371641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1492337263/10000000000 : ℝ)|^73 ≤ (4374616638681/50000000000000 : ℝ)^57
        have hw : |(-1492337263/10000000000 : ℝ)|=(1492337263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s3_s3_6 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5958118983/10000000000 : ℝ)*x 0 + (601303349/2000000000 : ℝ)*x 1 + (3599852043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5958118983/10000000000 : ℝ)^73 ≤ (805011246499/1562500000000 : ℝ)^57 := by
    have hnat : (5958118983 : ℕ)^73*1562500000000^57 ≤ 805011246499^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5958118983 10000000000 805011246499 1562500000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (601303349/2000000000 : ℝ)^73 ≤ (10728158365071/50000000000000 : ℝ)^57 := by
    have hnat : (601303349 : ℕ)^73*50000000000000^57 ≤ 10728158365071^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      601303349 2000000000 10728158365071 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3599852043/10000000000 : ℝ)^73 ≤ (2702296348683/10000000000000 : ℝ)^57 := by
    have hnat : (3599852043 : ℕ)^73*10000000000000^57 ≤ 2702296348683^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3599852043 10000000000 2702296348683 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5958118983/10000000000 : ℝ), (601303349/2000000000 : ℝ), (3599852043/10000000000 : ℝ)] ![(805011246499/1562500000000 : ℝ), (10728158365071/50000000000000 : ℝ), (2702296348683/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5958118983/10000000000 : ℝ)|^73 ≤ (805011246499/1562500000000 : ℝ)^57
        have hw : |(5958118983/10000000000 : ℝ)|=(5958118983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(601303349/2000000000 : ℝ)|^73 ≤ (10728158365071/50000000000000 : ℝ)^57
        have hw : |(601303349/2000000000 : ℝ)|=(601303349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3599852043/10000000000 : ℝ)|^73 ≤ (2702296348683/10000000000000 : ℝ)^57
        have hw : |(3599852043/10000000000 : ℝ)|=(3599852043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s3_s3_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-93012019/400000000 : ℝ)*x 0 + (4128914687/10000000000 : ℝ)*x 1 + (6032801561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (93012019/400000000 : ℝ)^73 ≤ (15440048021147/100000000000000 : ℝ)^57 := by
    have hnat : (93012019 : ℕ)^73*100000000000000^57 ≤ 15440048021147^57*400000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93012019 400000000 15440048021147 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4128914687/10000000000 : ℝ)^73 ≤ (6442143148667/20000000000000 : ℝ)^57 := by
    have hnat : (4128914687 : ℕ)^73*20000000000000^57 ≤ 6442143148667^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128914687 10000000000 6442143148667 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6032801561/10000000000 : ℝ)^73 ≤ (10469847244141/20000000000000 : ℝ)^57 := by
    have hnat : (6032801561 : ℕ)^73*20000000000000^57 ≤ 10469847244141^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6032801561 10000000000 10469847244141 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-93012019/400000000 : ℝ), (4128914687/10000000000 : ℝ), (6032801561/10000000000 : ℝ)] ![(15440048021147/100000000000000 : ℝ), (6442143148667/20000000000000 : ℝ), (10469847244141/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-93012019/400000000 : ℝ)|^73 ≤ (15440048021147/100000000000000 : ℝ)^57
        have hw : |(-93012019/400000000 : ℝ)|=(93012019/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4128914687/10000000000 : ℝ)|^73 ≤ (6442143148667/20000000000000 : ℝ)^57
        have hw : |(4128914687/10000000000 : ℝ)|=(4128914687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6032801561/10000000000 : ℝ)|^73 ≤ (10469847244141/20000000000000 : ℝ)^57
        have hw : |(6032801561/10000000000 : ℝ)|=(6032801561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s3_s3_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4460893253/10000000000 : ℝ)*x 0 + (-1989166721/10000000000 : ℝ)*x 1 + (2991390017/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4460893253/10000000000 : ℝ)^73 ≤ (35564272055139/100000000000000 : ℝ)^57 := by
    have hnat : (4460893253 : ℕ)^73*100000000000000^57 ≤ 35564272055139^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4460893253 10000000000 35564272055139 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1989166721/10000000000 : ℝ)^73 ≤ (12641742967897/100000000000000 : ℝ)^57 := by
    have hnat : (1989166721 : ℕ)^73*100000000000000^57 ≤ 12641742967897^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1989166721 10000000000 12641742967897 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2991390017/5000000000 : ℝ)^73 ≤ (25896992480243/50000000000000 : ℝ)^57 := by
    have hnat : (2991390017 : ℕ)^73*50000000000000^57 ≤ 25896992480243^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2991390017 5000000000 25896992480243 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4460893253/10000000000 : ℝ), (-1989166721/10000000000 : ℝ), (2991390017/5000000000 : ℝ)] ![(35564272055139/100000000000000 : ℝ), (12641742967897/100000000000000 : ℝ), (25896992480243/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4460893253/10000000000 : ℝ)|^73 ≤ (35564272055139/100000000000000 : ℝ)^57
        have hw : |(4460893253/10000000000 : ℝ)|=(4460893253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1989166721/10000000000 : ℝ)|^73 ≤ (12641742967897/100000000000000 : ℝ)^57
        have hw : |(-1989166721/10000000000 : ℝ)|=(1989166721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2991390017/5000000000 : ℝ)|^73 ≤ (25896992480243/50000000000000 : ℝ)^57
        have hw : |(2991390017/5000000000 : ℝ)|=(2991390017/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s3_s3_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4502308933/10000000000 : ℝ)*x 0 + (6590765293/10000000000 : ℝ)*x 1 + (-1021385587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4502308933/10000000000 : ℝ)^73 ≤ (7197537983603/20000000000000 : ℝ)^57 := by
    have hnat : (4502308933 : ℕ)^73*20000000000000^57 ≤ 7197537983603^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502308933 10000000000 7197537983603 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6590765293/10000000000 : ℝ)^73 ≤ (58628775042301/100000000000000 : ℝ)^57 := by
    have hnat : (6590765293 : ℕ)^73*100000000000000^57 ≤ 58628775042301^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6590765293 10000000000 58628775042301 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1021385587/10000000000 : ℝ)^73 ≤ (5383535022807/100000000000000 : ℝ)^57 := by
    have hnat : (1021385587 : ℕ)^73*100000000000000^57 ≤ 5383535022807^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021385587 10000000000 5383535022807 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4502308933/10000000000 : ℝ), (6590765293/10000000000 : ℝ), (-1021385587/10000000000 : ℝ)] ![(7197537983603/20000000000000 : ℝ), (58628775042301/100000000000000 : ℝ), (5383535022807/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4502308933/10000000000 : ℝ)|^73 ≤ (7197537983603/20000000000000 : ℝ)^57
        have hw : |(4502308933/10000000000 : ℝ)|=(4502308933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6590765293/10000000000 : ℝ)|^73 ≤ (58628775042301/100000000000000 : ℝ)^57
        have hw : |(6590765293/10000000000 : ℝ)|=(6590765293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1021385587/10000000000 : ℝ)|^73 ≤ (5383535022807/100000000000000 : ℝ)^57
        have hw : |(-1021385587/10000000000 : ℝ)|=(1021385587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s3_s3_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5988980797/10000000000 : ℝ)*x 0 + (1833008627/5000000000 : ℝ)*x 1 + (1449386893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5988980797/10000000000 : ℝ)^73 ≤ (51862744440193/100000000000000 : ℝ)^57 := by
    have hnat : (5988980797 : ℕ)^73*100000000000000^57 ≤ 51862744440193^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5988980797 10000000000 51862744440193 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1833008627/5000000000 : ℝ)^73 ≤ (27660698155879/100000000000000 : ℝ)^57 := by
    have hnat : (1833008627 : ℕ)^73*100000000000000^57 ≤ 27660698155879^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1833008627 5000000000 27660698155879 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1449386893/5000000000 : ℝ)^73 ≤ (20476557389269/100000000000000 : ℝ)^57 := by
    have hnat : (1449386893 : ℕ)^73*100000000000000^57 ≤ 20476557389269^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1449386893 5000000000 20476557389269 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5988980797/10000000000 : ℝ), (1833008627/5000000000 : ℝ), (1449386893/5000000000 : ℝ)] ![(51862744440193/100000000000000 : ℝ), (27660698155879/100000000000000 : ℝ), (20476557389269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5988980797/10000000000 : ℝ)|^73 ≤ (51862744440193/100000000000000 : ℝ)^57
        have hw : |(5988980797/10000000000 : ℝ)|=(5988980797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1833008627/5000000000 : ℝ)|^73 ≤ (27660698155879/100000000000000 : ℝ)^57
        have hw : |(1833008627/5000000000 : ℝ)|=(1833008627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1449386893/5000000000 : ℝ)|^73 ≤ (20476557389269/100000000000000 : ℝ)^57
        have hw : |(1449386893/5000000000 : ℝ)|=(1449386893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s3_s3_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1687180573/10000000000 : ℝ)*x 0 + (46389151/100000000 : ℝ)*x 1 + (6034648247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1687180573/10000000000 : ℝ)^73 ≤ (10238220102511/100000000000000 : ℝ)^57 := by
    have hnat : (1687180573 : ℕ)^73*100000000000000^57 ≤ 10238220102511^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1687180573 10000000000 10238220102511 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (46389151/100000000 : ℝ)^73 ≤ (4674002521351/12500000000000 : ℝ)^57 := by
    have hnat : (46389151 : ℕ)^73*12500000000000^57 ≤ 4674002521351^57*100000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      46389151 100000000 4674002521351 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6034648247/10000000000 : ℝ)^73 ≤ (26184879850939/50000000000000 : ℝ)^57 := by
    have hnat : (6034648247 : ℕ)^73*50000000000000^57 ≤ 26184879850939^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6034648247 10000000000 26184879850939 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1687180573/10000000000 : ℝ), (46389151/100000000 : ℝ), (6034648247/10000000000 : ℝ)] ![(10238220102511/100000000000000 : ℝ), (4674002521351/12500000000000 : ℝ), (26184879850939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1687180573/10000000000 : ℝ)|^73 ≤ (10238220102511/100000000000000 : ℝ)^57
        have hw : |(-1687180573/10000000000 : ℝ)|=(1687180573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(46389151/100000000 : ℝ)|^73 ≤ (4674002521351/12500000000000 : ℝ)^57
        have hw : |(46389151/100000000 : ℝ)|=(46389151/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6034648247/10000000000 : ℝ)|^73 ≤ (26184879850939/50000000000000 : ℝ)^57
        have hw : |(6034648247/10000000000 : ℝ)|=(6034648247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s3_s3_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (433597657/1000000000 : ℝ)*x 0 + (-1070567673/5000000000 : ℝ)*x 1 + (149615629/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (433597657/1000000000 : ℝ)^73 ≤ (34293877360633/100000000000000 : ℝ)^57 := by
    have hnat : (433597657 : ℕ)^73*100000000000000^57 ≤ 34293877360633^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      433597657 1000000000 34293877360633 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1070567673/5000000000 : ℝ)^73 ≤ (13891679382807/100000000000000 : ℝ)^57 := by
    have hnat : (1070567673 : ℕ)^73*100000000000000^57 ≤ 13891679382807^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070567673 5000000000 13891679382807 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (149615629/250000000 : ℝ)^73 ≤ (5181444324059/10000000000000 : ℝ)^57 := by
    have hnat : (149615629 : ℕ)^73*10000000000000^57 ≤ 5181444324059^57*250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149615629 250000000 5181444324059 10000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(433597657/1000000000 : ℝ), (-1070567673/5000000000 : ℝ), (149615629/250000000 : ℝ)] ![(34293877360633/100000000000000 : ℝ), (13891679382807/100000000000000 : ℝ), (5181444324059/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(433597657/1000000000 : ℝ)|^73 ≤ (34293877360633/100000000000000 : ℝ)^57
        have hw : |(433597657/1000000000 : ℝ)|=(433597657/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1070567673/5000000000 : ℝ)|^73 ≤ (13891679382807/100000000000000 : ℝ)^57
        have hw : |(-1070567673/5000000000 : ℝ)|=(1070567673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(149615629/250000000 : ℝ)|^73 ≤ (5181444324059/10000000000000 : ℝ)^57
        have hw : |(149615629/250000000 : ℝ)|=(149615629/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s3_s3_16 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2676937637/5000000000 : ℝ)*x 0 + (2896631417/5000000000 : ℝ)*x 1 + (-1019540521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676937637/5000000000 : ℝ)^73 ≤ (44926744641579/100000000000000 : ℝ)^57 := by
    have hnat : (2676937637 : ℕ)^73*100000000000000^57 ≤ 44926744641579^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676937637 5000000000 44926744641579 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2896631417/5000000000 : ℝ)^73 ≤ (12425542996479/25000000000000 : ℝ)^57 := by
    have hnat : (2896631417 : ℕ)^73*25000000000000^57 ≤ 12425542996479^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2896631417 5000000000 12425542996479 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1019540521/10000000000 : ℝ)^73 ≤ (671385419261/12500000000000 : ℝ)^57 := by
    have hnat : (1019540521 : ℕ)^73*12500000000000^57 ≤ 671385419261^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019540521 10000000000 671385419261 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676937637/5000000000 : ℝ), (2896631417/5000000000 : ℝ), (-1019540521/10000000000 : ℝ)] ![(44926744641579/100000000000000 : ℝ), (12425542996479/25000000000000 : ℝ), (671385419261/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676937637/5000000000 : ℝ)|^73 ≤ (44926744641579/100000000000000 : ℝ)^57
        have hw : |(2676937637/5000000000 : ℝ)|=(2676937637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2896631417/5000000000 : ℝ)|^73 ≤ (12425542996479/25000000000000 : ℝ)^57
        have hw : |(2896631417/5000000000 : ℝ)|=(2896631417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1019540521/10000000000 : ℝ)|^73 ≤ (671385419261/12500000000000 : ℝ)^57
        have hw : |(-1019540521/10000000000 : ℝ)|=(1019540521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s3_s3_20 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3390069861/5000000000 : ℝ)*x 0 + (169254667/625000000 : ℝ)*x 1 + (723615837/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3390069861/5000000000 : ℝ)^73 ≤ (30397442054171/50000000000000 : ℝ)^57 := by
    have hnat : (3390069861 : ℕ)^73*50000000000000^57 ≤ 30397442054171^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3390069861 5000000000 30397442054171 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169254667/625000000 : ℝ)^73 ≤ (9383772812829/50000000000000 : ℝ)^57 := by
    have hnat : (169254667 : ℕ)^73*50000000000000^57 ≤ 9383772812829^57*625000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169254667 625000000 9383772812829 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (723615837/2500000000 : ℝ)^73 ≤ (5109392563031/25000000000000 : ℝ)^57 := by
    have hnat : (723615837 : ℕ)^73*25000000000000^57 ≤ 5109392563031^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      723615837 2500000000 5109392563031 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3390069861/5000000000 : ℝ), (169254667/625000000 : ℝ), (723615837/2500000000 : ℝ)] ![(30397442054171/50000000000000 : ℝ), (9383772812829/50000000000000 : ℝ), (5109392563031/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3390069861/5000000000 : ℝ)|^73 ≤ (30397442054171/50000000000000 : ℝ)^57
        have hw : |(3390069861/5000000000 : ℝ)|=(3390069861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169254667/625000000 : ℝ)|^73 ≤ (9383772812829/50000000000000 : ℝ)^57
        have hw : |(169254667/625000000 : ℝ)|=(169254667/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(723615837/2500000000 : ℝ)|^73 ≤ (5109392563031/25000000000000 : ℝ)^57
        have hw : |(723615837/2500000000 : ℝ)|=(723615837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s3_s3_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-42276483/250000000 : ℝ)*x 0 + (4904448161/10000000000 : ℝ)*x 1 + (722730623/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42276483/250000000 : ℝ)^73 ≤ (10268373925603/100000000000000 : ℝ)^57 := by
    have hnat : (42276483 : ℕ)^73*100000000000000^57 ≤ 10268373925603^57*250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42276483 250000000 10268373925603 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4904448161/10000000000 : ℝ)^73 ≤ (20077436669709/50000000000000 : ℝ)^57 := by
    have hnat : (4904448161 : ℕ)^73*50000000000000^57 ≤ 20077436669709^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4904448161 10000000000 20077436669709 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (722730623/1250000000 : ℝ)^73 ≤ (991535054327/2000000000000 : ℝ)^57 := by
    have hnat : (722730623 : ℕ)^73*2000000000000^57 ≤ 991535054327^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      722730623 1250000000 991535054327 2000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-42276483/250000000 : ℝ), (4904448161/10000000000 : ℝ), (722730623/1250000000 : ℝ)] ![(10268373925603/100000000000000 : ℝ), (20077436669709/50000000000000 : ℝ), (991535054327/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-42276483/250000000 : ℝ)|^73 ≤ (10268373925603/100000000000000 : ℝ)^57
        have hw : |(-42276483/250000000 : ℝ)|=(42276483/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4904448161/10000000000 : ℝ)|^73 ≤ (20077436669709/50000000000000 : ℝ)^57
        have hw : |(4904448161/10000000000 : ℝ)|=(4904448161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(722730623/1250000000 : ℝ)|^73 ≤ (991535054327/2000000000000 : ℝ)^57
        have hw : |(722730623/1250000000 : ℝ)|=(722730623/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s3_s3_22 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5308579463/10000000000 : ℝ)*x 0 + (-878264839/5000000000 : ℝ)*x 1 + (2670071323/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5308579463/10000000000 : ℝ)^73 ≤ (22220266307087/50000000000000 : ℝ)^57 := by
    have hnat : (5308579463 : ℕ)^73*50000000000000^57 ≤ 22220266307087^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5308579463 10000000000 22220266307087 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (878264839/5000000000 : ℝ)^73 ≤ (10780253248641/100000000000000 : ℝ)^57 := by
    have hnat : (878264839 : ℕ)^73*100000000000000^57 ≤ 10780253248641^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      878264839 5000000000 10780253248641 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2670071323/5000000000 : ℝ)^73 ≤ (44779214115177/100000000000000 : ℝ)^57 := by
    have hnat : (2670071323 : ℕ)^73*100000000000000^57 ≤ 44779214115177^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2670071323 5000000000 44779214115177 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5308579463/10000000000 : ℝ), (-878264839/5000000000 : ℝ), (2670071323/5000000000 : ℝ)] ![(22220266307087/50000000000000 : ℝ), (10780253248641/100000000000000 : ℝ), (44779214115177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5308579463/10000000000 : ℝ)|^73 ≤ (22220266307087/50000000000000 : ℝ)^57
        have hw : |(5308579463/10000000000 : ℝ)|=(5308579463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-878264839/5000000000 : ℝ)|^73 ≤ (10780253248641/100000000000000 : ℝ)^57
        have hw : |(-878264839/5000000000 : ℝ)|=(878264839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2670071323/5000000000 : ℝ)|^73 ≤ (44779214115177/100000000000000 : ℝ)^57
        have hw : |(2670071323/5000000000 : ℝ)|=(2670071323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s3_s3_23 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2157107453/5000000000 : ℝ)*x 0 + (6525568271/10000000000 : ℝ)*x 1 + (-1396923383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2157107453/5000000000 : ℝ)^73 ≤ (34073603291847/100000000000000 : ℝ)^57 := by
    have hnat : (2157107453 : ℕ)^73*100000000000000^57 ≤ 34073603291847^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2157107453 5000000000 34073603291847 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6525568271/10000000000 : ℝ)^73 ≤ (2894352245989/5000000000000 : ℝ)^57 := by
    have hnat : (6525568271 : ℕ)^73*5000000000000^57 ≤ 2894352245989^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6525568271 10000000000 2894352245989 5000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1396923383/10000000000 : ℝ)^73 ≤ (25122974307/312500000000 : ℝ)^57 := by
    have hnat : (1396923383 : ℕ)^73*312500000000^57 ≤ 25122974307^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1396923383 10000000000 25122974307 312500000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2157107453/5000000000 : ℝ), (6525568271/10000000000 : ℝ), (-1396923383/10000000000 : ℝ)] ![(34073603291847/100000000000000 : ℝ), (2894352245989/5000000000000 : ℝ), (25122974307/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2157107453/5000000000 : ℝ)|^73 ≤ (34073603291847/100000000000000 : ℝ)^57
        have hw : |(2157107453/5000000000 : ℝ)|=(2157107453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6525568271/10000000000 : ℝ)|^73 ≤ (2894352245989/5000000000000 : ℝ)^57
        have hw : |(6525568271/10000000000 : ℝ)|=(6525568271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1396923383/10000000000 : ℝ)|^73 ≤ (25122974307/312500000000 : ℝ)^57
        have hw : |(-1396923383/10000000000 : ℝ)|=(1396923383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312061_s3_s3_27 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (692787017/1000000000 : ℝ)*x 0 + (2549026547/10000000000 : ℝ)*x 1 + (2861035103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (692787017/1000000000 : ℝ)^73 ≤ (15624129014189/25000000000000 : ℝ)^57 := by
    have hnat : (692787017 : ℕ)^73*25000000000000^57 ≤ 15624129014189^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      692787017 1000000000 15624129014189 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2549026547/10000000000 : ℝ)^73 ≤ (17367711625589/100000000000000 : ℝ)^57 := by
    have hnat : (2549026547 : ℕ)^73*100000000000000^57 ≤ 17367711625589^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2549026547 10000000000 17367711625589 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2861035103/10000000000 : ℝ)^73 ≤ (1258485768217/6250000000000 : ℝ)^57 := by
    have hnat : (2861035103 : ℕ)^73*6250000000000^57 ≤ 1258485768217^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2861035103 10000000000 1258485768217 6250000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(692787017/1000000000 : ℝ), (2549026547/10000000000 : ℝ), (2861035103/10000000000 : ℝ)] ![(15624129014189/25000000000000 : ℝ), (17367711625589/100000000000000 : ℝ), (1258485768217/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(692787017/1000000000 : ℝ)|^73 ≤ (15624129014189/25000000000000 : ℝ)^57
        have hw : |(692787017/1000000000 : ℝ)|=(692787017/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2549026547/10000000000 : ℝ)|^73 ≤ (17367711625589/100000000000000 : ℝ)^57
        have hw : |(2549026547/10000000000 : ℝ)|=(2549026547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2861035103/10000000000 : ℝ)|^73 ≤ (1258485768217/6250000000000 : ℝ)^57
        have hw : |(2861035103/10000000000 : ℝ)|=(2861035103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312061_s3 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((43551/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43551/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(50089/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(50089/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(45181/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(45181/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((22839/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22839/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13959/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13959/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6447/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6447/25000 : ℝ)*X 1 2) := by
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
  have main1 : (78337/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78337/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
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
  have s3_pow0 : (43551/100000 : ℝ) ^ (9/2 : ℝ) ≤ (237405945999017861/10000000000000000000 : ℝ) := by
    have hpowers : (43551/100000 : ℝ)^9 ≤ (237405945999017861/10000000000000000000 : ℝ)^2 := by
      have hnat : (43551 : ℕ)^9*10000000000000000000^2 ≤ 237405945999017861^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43551 100000 237405945999017861 10000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (43551/100000 : ℝ)) (X := (237405945999017861/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s3_corner0a : (10237405945999017861/10000000000000000000 : ℝ) ≤ (10052276542915251/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (10237405945999017861/10000000000000000000 : ℝ)^2 ≤ (10052276542915251/10000000000000000 : ℝ)^9 := by
      have hnat : (10237405945999017861 : ℕ)^2*10000000000000000^9 ≤ 10052276542915251^9*10000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10237405945999017861 10000000000000000000 10052276542915251 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10052276542915251/10000000000000000 : ℝ)) (X := (10237405945999017861/10000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s3_corner0b : (5237405945999017861/5000000000000000000 : ℝ) ≤ (1262952315803249/1250000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (5237405945999017861/5000000000000000000 : ℝ)^2 ≤ (1262952315803249/1250000000000000 : ℝ)^9 := by
      have hnat : (5237405945999017861 : ℕ)^2*1250000000000000^9 ≤ 1262952315803249^9*5000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5237405945999017861 5000000000000000000 1262952315803249 1250000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1262952315803249/1250000000000000 : ℝ)) (X := (5237405945999017861/5000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(52276542915251/4355100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(51341983510741/4355100000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (43551/100000 : ℝ)) (alpha := (52276542915251/4355100000000000 : ℝ)) (beta := (51341983510741/4355100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (43551/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(52276542915251/4355100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(51341983510741/4355100000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (50089/100000 : ℝ) ^ (9/2 : ℝ) ≤ (4454927348870788161/100000000000000000000 : ℝ) := by
    have hpowers : (50089/100000 : ℝ)^9 ≤ (4454927348870788161/100000000000000000000 : ℝ)^2 := by
      have hnat : (50089 : ℕ)^9*100000000000000000000^2 ≤ 4454927348870788161^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50089 100000 4454927348870788161 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (50089/100000 : ℝ)) (X := (4454927348870788161/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s3_corner1a : (104454927348870788161/100000000000000000000 : ℝ) ≤ (2524331797408603/2500000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (104454927348870788161/100000000000000000000 : ℝ)^2 ≤ (2524331797408603/2500000000000000 : ℝ)^9 := by
      have hnat : (104454927348870788161 : ℕ)^2*2500000000000000^9 ≤ 2524331797408603^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104454927348870788161 100000000000000000000 2524331797408603 2500000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2524331797408603/2500000000000000 : ℝ)) (X := (104454927348870788161/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s3_corner1b : (54454927348870788161/50000000000000000000 : ℝ) ≤ (5095738759336619/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (54454927348870788161/50000000000000000000 : ℝ)^2 ≤ (5095738759336619/5000000000000000 : ℝ)^9 := by
      have hnat : (54454927348870788161 : ℕ)^2*5000000000000000^9 ≤ 5095738759336619^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54454927348870788161 50000000000000000000 5095738759336619 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5095738759336619/5000000000000000 : ℝ)) (X := (54454927348870788161/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(24331797408603/1252225000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(47075164519413/2504450000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (50089/100000 : ℝ)) (alpha := (24331797408603/1252225000000000 : ℝ)) (beta := (47075164519413/2504450000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (50089/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(24331797408603/1252225000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(47075164519413/2504450000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (45181/100000 : ℝ) ^ (9/2 : ℝ) ≤ (2800923682009071301/100000000000000000000 : ℝ) := by
    have hpowers : (45181/100000 : ℝ)^9 ≤ (2800923682009071301/100000000000000000000 : ℝ)^2 := by
      have hnat : (45181 : ℕ)^9*100000000000000000000^2 ≤ 2800923682009071301^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        45181 100000 2800923682009071301 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (45181/100000 : ℝ)) (X := (2800923682009071301/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s3_corner2a : (102800923682009071301/100000000000000000000 : ℝ) ≤ (2515393952326481/2500000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (102800923682009071301/100000000000000000000 : ℝ)^2 ≤ (2515393952326481/2500000000000000 : ℝ)^9 := by
      have hnat : (102800923682009071301 : ℕ)^2*2500000000000000^9 ≤ 2515393952326481^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102800923682009071301 100000000000000000000 2515393952326481 2500000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2515393952326481/2500000000000000 : ℝ)) (X := (102800923682009071301/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s3_corner2b : (52800923682009071301/50000000000000000000 : ℝ) ≤ (10121860249925713/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (52800923682009071301/50000000000000000000 : ℝ)^2 ≤ (10121860249925713/10000000000000000 : ℝ)^9 := by
      have hnat : (52800923682009071301 : ℕ)^2*10000000000000000^9 ≤ 10121860249925713^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52800923682009071301 50000000000000000000 10121860249925713 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10121860249925713/10000000000000000 : ℝ)) (X := (52800923682009071301/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(15393952326481/1129525000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(60284440619789/4518100000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (45181/100000 : ℝ)) (alpha := (15393952326481/1129525000000000 : ℝ)) (beta := (60284440619789/4518100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (45181/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(15393952326481/1129525000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(60284440619789/4518100000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-2305791233/10000000000 : ℝ)*X 0 0+(4489485801/10000000000 : ℝ)*X 0 1+(5717310777/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((1168679957/2500000000 : ℝ)*X 1 0+(-23691619/100000000 : ℝ)*X 1 1+(1098537393/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((943204901/2000000000 : ℝ)*X 2 0+(3048371641/5000000000 : ℝ)*X 2 1+(-1492337263/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((5958118983/10000000000 : ℝ)*X 0 0+(601303349/2000000000 : ℝ)*X 0 1+(3599852043/10000000000 : ℝ)*X 0 2+(5958118983/10000000000 : ℝ)*X 1 0+(601303349/2000000000 : ℝ)*X 1 1+(3599852043/10000000000 : ℝ)*X 1 2+(5958118983/10000000000 : ℝ)*X 2 0+(601303349/2000000000 : ℝ)*X 2 1+(3599852043/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-93012019/400000000 : ℝ)*X 0 0+(4128914687/10000000000 : ℝ)*X 0 1+(6032801561/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((4460893253/10000000000 : ℝ)*X 1 0+(-1989166721/10000000000 : ℝ)*X 1 1+(2991390017/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((4502308933/10000000000 : ℝ)*X 2 0+(6590765293/10000000000 : ℝ)*X 2 1+(-1021385587/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((5988980797/10000000000 : ℝ)*X 0 0+(1833008627/5000000000 : ℝ)*X 0 1+(1449386893/5000000000 : ℝ)*X 0 2+(5988980797/10000000000 : ℝ)*X 1 0+(1833008627/5000000000 : ℝ)*X 1 1+(1449386893/5000000000 : ℝ)*X 1 2+(5988980797/10000000000 : ℝ)*X 2 0+(1833008627/5000000000 : ℝ)*X 2 1+(1449386893/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-1687180573/10000000000 : ℝ)*X 0 0+(46389151/100000000 : ℝ)*X 0 1+(6034648247/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((433597657/1000000000 : ℝ)*X 1 0+(-1070567673/5000000000 : ℝ)*X 1 1+(149615629/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((2676937637/5000000000 : ℝ)*X 2 0+(2896631417/5000000000 : ℝ)*X 2 1+(-1019540521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((3390069861/5000000000 : ℝ)*X 0 0+(169254667/625000000 : ℝ)*X 0 1+(723615837/2500000000 : ℝ)*X 0 2+(3390069861/5000000000 : ℝ)*X 1 0+(169254667/625000000 : ℝ)*X 1 1+(723615837/2500000000 : ℝ)*X 1 2+(3390069861/5000000000 : ℝ)*X 2 0+(169254667/625000000 : ℝ)*X 2 1+(723615837/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-42276483/250000000 : ℝ)*X 0 0+(4904448161/10000000000 : ℝ)*X 0 1+(722730623/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((5308579463/10000000000 : ℝ)*X 1 0+(-878264839/5000000000 : ℝ)*X 1 1+(2670071323/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((2157107453/5000000000 : ℝ)*X 2 0+(6525568271/10000000000 : ℝ)*X 2 1+(-1396923383/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((692787017/1000000000 : ℝ)*X 0 0+(2549026547/10000000000 : ℝ)*X 0 1+(2861035103/10000000000 : ℝ)*X 0 2+(692787017/1000000000 : ℝ)*X 1 0+(2549026547/10000000000 : ℝ)*X 1 1+(2861035103/10000000000 : ℝ)*X 1 2+(692787017/1000000000 : ℝ)*X 2 0+(2549026547/10000000000 : ℝ)*X 2 1+(2861035103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312061_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((22839/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22839/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (16674217925608029294287372901331/1642650164467650000000000000000000000 : ℝ) := by norm_num
    linear_combination (3495263/1000000000000 : ℝ)*(base50) + (360151402369/250000000000 : ℝ)*(base59) + (4967991/1000000000000 : ℝ)*(base60) + (3819045404497/500000000000 : ℝ)*(major_s3_0) + (3819045404497/500000000000 : ℝ)*(major_s3_1) + (3819045404497/500000000000 : ℝ)*(major_s3_2) + (10503979/200000000000 : ℝ)*(sp_s3_0) + (51565187/1000000000000 : ℝ)*(sp_s3_6) + (535001734581/50000000000 : ℝ)*(sp_s3_7) + (10699794158859/1000000000000 : ℝ)*(sp_s3_8) + (334372937477/31250000000 : ℝ)*(sp_s3_9) + (4576039457677/1000000000000 : ℝ)*(sp_s3_13) + (58610531/200000000000 : ℝ)*(sp_s3_15) + (612849/4000000000 : ℝ)*(sp_s3_23) + (286005688929/62500000000 : ℝ)*(f.failure) + (5350043605757/500000000000 : ℝ)*(f.sum) + (40344369909041054899/113153555450000000000000000000000 : ℝ)*base62 + (937884349533873/2259050000000000000000000000 : ℝ)*base64 + (136272334454603/626112500000000000000000000 : ℝ)*base67 + (151995390479593/2259050000000000000000000000 : ℝ)*base69 + (7027935418306377799/24595971637500000000000000000000 : ℝ)*base70 + (497016709818341/1088775000000000000000000000 : ℝ)*base73 + (280529598997937/1252225000000000000000000000 : ℝ)*base75 + (508635996740311/1088775000000000000000000000 : ℝ)*base77 + (111418079165972819/218142603900000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (6323/6250000000000000 : ℝ)*base86 + (6323/6250000000000000 : ℝ)*base88 + (6323/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13959/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13959/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (18884645699763462952742765232821/1642650164467650000000000000000000000 : ℝ) := by norm_num
    linear_combination (406701/500000000000 : ℝ)*(base39) + (685047/1000000000000 : ℝ)*(base49) + (199373929271/200000000000 : ℝ)*(base59) + (3655147203247/500000000000 : ℝ)*(major_s3_0) + (3655147203247/500000000000 : ℝ)*(major_s3_1) + (3655147203247/500000000000 : ℝ)*(major_s3_2) + (39819401/1000000000000 : ℝ)*(sp_s3_2) + (8094453/125000000000 : ℝ)*(sp_s3_6) + (41418773/500000000000 : ℝ)*(sp_s3_7) + (10240798701079/1000000000000 : ℝ)*(sp_s3_14) + (160013774041/15625000000 : ℝ)*(sp_s3_15) + (10240841719223/1000000000000 : ℝ)*(sp_s3_16) + (2189577767477/500000000000 : ℝ)*(sp_s3_20) + (483151631/1000000000000 : ℝ)*(sp_s3_27) + (4379703442209/1000000000000 : ℝ)*(f.failure) + (160013774041/15625000000 : ℝ)*(f.sum) + (1650965961215295409/113153555450000000000000000000000 : ℝ)*base62 + (792128131042409/1129525000000000000000000000 : ℝ)*base64 + (1049010320417499/1252225000000000000000000000 : ℝ)*base66 + (126840454283789/1129525000000000000000000000 : ℝ)*base69 + (58645455566843032831/98383886550000000000000000000000 : ℝ)*base70 + (13217374058063/136096875000000000000000000 : ℝ)*base72 + (349349436830399/2504450000000000000000000000 : ℝ)*base75 + (259780314484651/1088775000000000000000000000 : ℝ)*base77 + (4966623923068707541/5453565097500000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (30817/100000000000000000 : ℝ)*base87 + (30817/100000000000000000 : ℝ)*base89 + (30817/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6447/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6447/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (382014918290539924467810346591/36503336988170000000000000000000000 : ℝ) := by norm_num
    linear_combination (3287351/500000000000 : ℝ)*(base15) + (15126068201/40000000000 : ℝ)*(base40) + (1012316674981/1000000000000 : ℝ)*(base59) + (1378370114059/200000000000 : ℝ)*(major_s3_0) + (1378370114059/200000000000 : ℝ)*(major_s3_1) + (1378370114059/200000000000 : ℝ)*(major_s3_2) + (32745017/125000000000 : ℝ)*(sp_s3_0) + (274253947/1000000000000 : ℝ)*(sp_s3_1) + (1084399/100000000000 : ℝ)*(sp_s3_2) + (1671773/31250000000 : ℝ)*(sp_s3_9) + (4827214011601/500000000000 : ℝ)*(sp_s3_21) + (9654409154689/1000000000000 : ℝ)*(sp_s3_22) + (2413656410653/250000000000 : ℝ)*(sp_s3_23) + (2064503834421/500000000000 : ℝ)*(sp_s3_27) + (2064503834421/500000000000 : ℝ)*(f.failure) + (4827344991669/500000000000 : ℝ)*(f.sum) + (600548940717770957/5657677772500000000000000000000 : ℝ)*base63 + (169437713467373/180724000000000000000000000 : ℝ)*base65 + (274580841427593/500890000000000000000000000 : ℝ)*base67 + (60778582854831/90362000000000000000000000 : ℝ)*base69 + (4581251874231111461/9838388655000000000000000000000 : ℝ)*base71 + (438118568357869/871020000000000000000000000 : ℝ)*base73 + (18997741597619/31305625000000000000000000 : ℝ)*base75 + (461004683047901/871020000000000000000000000 : ℝ)*base77 + (3397267683547469041/43628520780000000000000000000000 : ℝ)*base79 + (37627/50000000000000000 : ℝ)*base86 + (37627/50000000000000000 : ℝ)*base88 + (37627/50000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((43551/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43551/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(50089/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(50089/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(45181/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(45181/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((22839/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22839/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13959/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13959/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6447/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6447/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c312061_s3 p hpa hpb X hX hprev2

#print axioms solution
