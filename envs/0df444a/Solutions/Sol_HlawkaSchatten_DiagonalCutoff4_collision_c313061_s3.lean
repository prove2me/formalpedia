-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c313061_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:34:50.171321+00:00
-- url     : https://prove2.me/submissions/5bac1e79-e6d1-4113-9f9c-cbaece7faebc

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
theorem collision_support_c313061_s3_s3_0 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-291942911/1250000000 : ℝ)*x 0 + (895653853/2000000000 : ℝ)*x 1 + (1133949817/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (291942911/1250000000 : ℝ)^37 ≤ (15636880104711/100000000000000 : ℝ)^29 := by
    have hnat : (291942911 : ℕ)^37*100000000000000^29 ≤ 15636880104711^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291942911 1250000000 15636880104711 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (895653853/2000000000 : ℝ)^37 ≤ (35881016796229/100000000000000 : ℝ)^29 := by
    have hnat : (895653853 : ℕ)^37*100000000000000^29 ≤ 35881016796229^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      895653853 2000000000 35881016796229 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1133949817/2000000000 : ℝ)^37 ≤ (48482103070809/100000000000000 : ℝ)^29 := by
    have hnat : (1133949817 : ℕ)^37*100000000000000^29 ≤ 48482103070809^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133949817 2000000000 48482103070809 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-291942911/1250000000 : ℝ), (895653853/2000000000 : ℝ), (1133949817/2000000000 : ℝ)] ![(15636880104711/100000000000000 : ℝ), (35881016796229/100000000000000 : ℝ), (48482103070809/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-291942911/1250000000 : ℝ)|^37 ≤ (15636880104711/100000000000000 : ℝ)^29
        have hw : |(-291942911/1250000000 : ℝ)|=(291942911/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(895653853/2000000000 : ℝ)|^37 ≤ (35881016796229/100000000000000 : ℝ)^29
        have hw : |(895653853/2000000000 : ℝ)|=(895653853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1133949817/2000000000 : ℝ)|^37 ≤ (48482103070809/100000000000000 : ℝ)^29
        have hw : |(1133949817/2000000000 : ℝ)|=(1133949817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s3_s3_1 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4664095561/10000000000 : ℝ)*x 0 + (-297525861/1250000000 : ℝ)*x 1 + (2729243209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4664095561/10000000000 : ℝ)^37 ≤ (37791396498989/100000000000000 : ℝ)^29 := by
    have hnat : (4664095561 : ℕ)^37*100000000000000^29 ≤ 37791396498989^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4664095561 10000000000 37791396498989 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (297525861/1250000000 : ℝ)^37 ≤ (16019403888031/100000000000000 : ℝ)^29 := by
    have hnat : (297525861 : ℕ)^37*100000000000000^29 ≤ 16019403888031^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297525861 1250000000 16019403888031 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2729243209/5000000000 : ℝ)^37 ≤ (46189199595961/100000000000000 : ℝ)^29 := by
    have hnat : (2729243209 : ℕ)^37*100000000000000^29 ≤ 46189199595961^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729243209 5000000000 46189199595961 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4664095561/10000000000 : ℝ), (-297525861/1250000000 : ℝ), (2729243209/5000000000 : ℝ)] ![(37791396498989/100000000000000 : ℝ), (16019403888031/100000000000000 : ℝ), (46189199595961/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4664095561/10000000000 : ℝ)|^37 ≤ (37791396498989/100000000000000 : ℝ)^29
        have hw : |(4664095561/10000000000 : ℝ)|=(4664095561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-297525861/1250000000 : ℝ)|^37 ≤ (16019403888031/100000000000000 : ℝ)^29
        have hw : |(-297525861/1250000000 : ℝ)|=(297525861/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2729243209/5000000000 : ℝ)|^37 ≤ (46189199595961/100000000000000 : ℝ)^29
        have hw : |(2729243209/5000000000 : ℝ)|=(2729243209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s3_s3_2 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (293049027/625000000 : ℝ)*x 0 + (605651073/1000000000 : ℝ)*x 1 + (-38568721/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (293049027/625000000 : ℝ)^37 ≤ (19023405933871/50000000000000 : ℝ)^29 := by
    have hnat : (293049027 : ℕ)^37*50000000000000^29 ≤ 19023405933871^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      293049027 625000000 19023405933871 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (605651073/1000000000 : ℝ)^37 ≤ (52740705719777/100000000000000 : ℝ)^29 := by
    have hnat : (605651073 : ℕ)^37*100000000000000^29 ≤ 52740705719777^29*1000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605651073 1000000000 52740705719777 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (38568721/250000000 : ℝ)^37 ≤ (4606241197079/50000000000000 : ℝ)^29 := by
    have hnat : (38568721 : ℕ)^37*50000000000000^29 ≤ 4606241197079^29*250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38568721 250000000 4606241197079 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(293049027/625000000 : ℝ), (605651073/1000000000 : ℝ), (-38568721/250000000 : ℝ)] ![(19023405933871/50000000000000 : ℝ), (52740705719777/100000000000000 : ℝ), (4606241197079/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(293049027/625000000 : ℝ)|^37 ≤ (19023405933871/50000000000000 : ℝ)^29
        have hw : |(293049027/625000000 : ℝ)|=(293049027/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(605651073/1000000000 : ℝ)|^37 ≤ (52740705719777/100000000000000 : ℝ)^29
        have hw : |(605651073/1000000000 : ℝ)|=(605651073/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-38568721/250000000 : ℝ)|^37 ≤ (4606241197079/50000000000000 : ℝ)^29
        have hw : |(-38568721/250000000 : ℝ)|=(38568721/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s3_s3_6 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1484298293/2500000000 : ℝ)*x 0 + (12012387/40000000 : ℝ)*x 1 + (3586781343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1484298293/2500000000 : ℝ)^37 ≤ (51418667164097/100000000000000 : ℝ)^29 := by
    have hnat : (1484298293 : ℕ)^37*100000000000000^29 ≤ 51418667164097^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1484298293 2500000000 51418667164097 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12012387/40000000 : ℝ)^37 ≤ (10775080443001/50000000000000 : ℝ)^29 := by
    have hnat : (12012387 : ℕ)^37*50000000000000^29 ≤ 10775080443001^29*40000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12012387 40000000 10775080443001 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3586781343/10000000000 : ℝ)^37 ≤ (3378896492887/12500000000000 : ℝ)^29 := by
    have hnat : (3586781343 : ℕ)^37*12500000000000^29 ≤ 3378896492887^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3586781343 10000000000 3378896492887 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1484298293/2500000000 : ℝ), (12012387/40000000 : ℝ), (3586781343/10000000000 : ℝ)] ![(51418667164097/100000000000000 : ℝ), (10775080443001/50000000000000 : ℝ), (3378896492887/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1484298293/2500000000 : ℝ)|^37 ≤ (51418667164097/100000000000000 : ℝ)^29
        have hw : |(1484298293/2500000000 : ℝ)|=(1484298293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(12012387/40000000 : ℝ)|^37 ≤ (10775080443001/50000000000000 : ℝ)^29
        have hw : |(12012387/40000000 : ℝ)|=(12012387/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3586781343/10000000000 : ℝ)|^37 ≤ (3378896492887/12500000000000 : ℝ)^29
        have hw : |(3586781343/10000000000 : ℝ)|=(3586781343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s3_s3_7 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-18347821/78125000 : ℝ)*x 0 + (4313631187/10000000000 : ℝ)*x 1 + (1453140631/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (18347821/78125000 : ℝ)^37 ≤ (15747822943439/100000000000000 : ℝ)^29 := by
    have hnat : (18347821 : ℕ)^37*100000000000000^29 ≤ 15747822943439^29*78125000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18347821 78125000 15747822943439 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4313631187/10000000000 : ℝ)^37 ≤ (34206610916349/100000000000000 : ℝ)^29 := by
    have hnat : (4313631187 : ℕ)^37*100000000000000^29 ≤ 34206610916349^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4313631187 10000000000 34206610916349 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1453140631/2500000000 : ℝ)^37 ≤ (5004556612831/10000000000000 : ℝ)^29 := by
    have hnat : (1453140631 : ℕ)^37*10000000000000^29 ≤ 5004556612831^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1453140631 2500000000 5004556612831 10000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-18347821/78125000 : ℝ), (4313631187/10000000000 : ℝ), (1453140631/2500000000 : ℝ)] ![(15747822943439/100000000000000 : ℝ), (34206610916349/100000000000000 : ℝ), (5004556612831/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-18347821/78125000 : ℝ)|^37 ≤ (15747822943439/100000000000000 : ℝ)^29
        have hw : |(-18347821/78125000 : ℝ)|=(18347821/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4313631187/10000000000 : ℝ)|^37 ≤ (34206610916349/100000000000000 : ℝ)^29
        have hw : |(4313631187/10000000000 : ℝ)|=(4313631187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1453140631/2500000000 : ℝ)|^37 ≤ (5004556612831/10000000000000 : ℝ)^29
        have hw : |(1453140631/2500000000 : ℝ)|=(1453140631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s3_s3_8 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1136254717/2500000000 : ℝ)*x 0 + (-2113856259/10000000000 : ℝ)*x 1 + (5778040269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1136254717/2500000000 : ℝ)^37 ≤ (9141191058911/25000000000000 : ℝ)^29 := by
    have hnat : (1136254717 : ℕ)^37*25000000000000^29 ≤ 9141191058911^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136254717 2500000000 9141191058911 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2113856259/10000000000 : ℝ)^37 ≤ (13768586902981/100000000000000 : ℝ)^29 := by
    have hnat : (2113856259 : ℕ)^37*100000000000000^29 ≤ 13768586902981^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2113856259 10000000000 13768586902981 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5778040269/10000000000 : ℝ)^37 ≤ (49666648843403/100000000000000 : ℝ)^29 := by
    have hnat : (5778040269 : ℕ)^37*100000000000000^29 ≤ 49666648843403^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5778040269 10000000000 49666648843403 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1136254717/2500000000 : ℝ), (-2113856259/10000000000 : ℝ), (5778040269/10000000000 : ℝ)] ![(9141191058911/25000000000000 : ℝ), (13768586902981/100000000000000 : ℝ), (49666648843403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1136254717/2500000000 : ℝ)|^37 ≤ (9141191058911/25000000000000 : ℝ)^29
        have hw : |(1136254717/2500000000 : ℝ)|=(1136254717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2113856259/10000000000 : ℝ)|^37 ≤ (13768586902981/100000000000000 : ℝ)^29
        have hw : |(-2113856259/10000000000 : ℝ)|=(2113856259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5778040269/10000000000 : ℝ)|^37 ≤ (49666648843403/100000000000000 : ℝ)^29
        have hw : |(5778040269/10000000000 : ℝ)|=(5778040269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s3_s3_9 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (285608279/625000000 : ℝ)*x 0 + (1274565167/2000000000 : ℝ)*x 1 + (-1230191923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (285608279/625000000 : ℝ)^37 ≤ (4602327858017/12500000000000 : ℝ)^29 := by
    have hnat : (285608279 : ℕ)^37*12500000000000^29 ≤ 4602327858017^29*625000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285608279 625000000 4602327858017 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1274565167/2000000000 : ℝ)^37 ≤ (28140038572187/50000000000000 : ℝ)^29 := by
    have hnat : (1274565167 : ℕ)^37*50000000000000^29 ≤ 28140038572187^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1274565167 2000000000 28140038572187 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1230191923/10000000000 : ℝ)^37 ≤ (6901299969837/100000000000000 : ℝ)^29 := by
    have hnat : (1230191923 : ℕ)^37*100000000000000^29 ≤ 6901299969837^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1230191923 10000000000 6901299969837 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(285608279/625000000 : ℝ), (1274565167/2000000000 : ℝ), (-1230191923/10000000000 : ℝ)] ![(4602327858017/12500000000000 : ℝ), (28140038572187/50000000000000 : ℝ), (6901299969837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(285608279/625000000 : ℝ)|^37 ≤ (4602327858017/12500000000000 : ℝ)^29
        have hw : |(285608279/625000000 : ℝ)|=(285608279/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1274565167/2000000000 : ℝ)|^37 ≤ (28140038572187/50000000000000 : ℝ)^29
        have hw : |(1274565167/2000000000 : ℝ)|=(1274565167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1230191923/10000000000 : ℝ)|^37 ≤ (6901299969837/100000000000000 : ℝ)^29
        have hw : |(-1230191923/10000000000 : ℝ)|=(1230191923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s3_s3_13 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5962629373/10000000000 : ℝ)*x 0 + (826994813/2500000000 : ℝ)*x 1 + (1629517013/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5962629373/10000000000 : ℝ)^37 ≤ (25849945427999/50000000000000 : ℝ)^29 := by
    have hnat : (5962629373 : ℕ)^37*50000000000000^29 ≤ 25849945427999^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5962629373 10000000000 25849945427999 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (826994813/2500000000 : ℝ)^37 ≤ (6094925188133/25000000000000 : ℝ)^29 := by
    have hnat : (826994813 : ℕ)^37*25000000000000^29 ≤ 6094925188133^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826994813 2500000000 6094925188133 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1629517013/5000000000 : ℝ)^37 ≤ (23920408379979/100000000000000 : ℝ)^29 := by
    have hnat : (1629517013 : ℕ)^37*100000000000000^29 ≤ 23920408379979^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1629517013 5000000000 23920408379979 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5962629373/10000000000 : ℝ), (826994813/2500000000 : ℝ), (1629517013/5000000000 : ℝ)] ![(25849945427999/50000000000000 : ℝ), (6094925188133/25000000000000 : ℝ), (23920408379979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5962629373/10000000000 : ℝ)|^37 ≤ (25849945427999/50000000000000 : ℝ)^29
        have hw : |(5962629373/10000000000 : ℝ)|=(5962629373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(826994813/2500000000 : ℝ)|^37 ≤ (6094925188133/25000000000000 : ℝ)^29
        have hw : |(826994813/2500000000 : ℝ)|=(826994813/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1629517013/5000000000 : ℝ)|^37 ≤ (23920408379979/100000000000000 : ℝ)^29
        have hw : |(1629517013/5000000000 : ℝ)|=(1629517013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s3_s3_14 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-961538807/5000000000 : ℝ)*x 0 + (2322137279/5000000000 : ℝ)*x 1 + (2913765321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (961538807/5000000000 : ℝ)^37 ≤ (12203339445447/100000000000000 : ℝ)^29 := by
    have hnat : (961538807 : ℕ)^37*100000000000000^29 ≤ 12203339445447^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961538807 5000000000 12203339445447 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2322137279/5000000000 : ℝ)^37 ≤ (37586610647/100000000000 : ℝ)^29 := by
    have hnat : (2322137279 : ℕ)^37*100000000000^29 ≤ 37586610647^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2322137279 5000000000 37586610647 100000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2913765321/5000000000 : ℝ)^37 ≤ (12552512472309/25000000000000 : ℝ)^29 := by
    have hnat : (2913765321 : ℕ)^37*25000000000000^29 ≤ 12552512472309^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2913765321 5000000000 12552512472309 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-961538807/5000000000 : ℝ), (2322137279/5000000000 : ℝ), (2913765321/5000000000 : ℝ)] ![(12203339445447/100000000000000 : ℝ), (37586610647/100000000000 : ℝ), (12552512472309/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-961538807/5000000000 : ℝ)|^37 ≤ (12203339445447/100000000000000 : ℝ)^29
        have hw : |(-961538807/5000000000 : ℝ)|=(961538807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2322137279/5000000000 : ℝ)|^37 ≤ (37586610647/100000000000 : ℝ)^29
        have hw : |(2322137279/5000000000 : ℝ)|=(2322137279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2913765321/5000000000 : ℝ)|^37 ≤ (12552512472309/25000000000000 : ℝ)^29
        have hw : |(2913765321/5000000000 : ℝ)|=(2913765321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s3_s3_15 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4449100741/10000000000 : ℝ)*x 0 + (-446697021/2000000000 : ℝ)*x 1 + (5776202371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4449100741/10000000000 : ℝ)^37 ≤ (1779155453729/5000000000000 : ℝ)^29 := by
    have hnat : (4449100741 : ℕ)^37*5000000000000^29 ≤ 1779155453729^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4449100741 10000000000 1779155453729 5000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (446697021/2000000000 : ℝ)^37 ≤ (2954079483/20000000000 : ℝ)^29 := by
    have hnat : (446697021 : ℕ)^37*20000000000^29 ≤ 2954079483^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446697021 2000000000 2954079483 20000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5776202371/10000000000 : ℝ)^37 ≤ (49646493492249/100000000000000 : ℝ)^29 := by
    have hnat : (5776202371 : ℕ)^37*100000000000000^29 ≤ 49646493492249^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5776202371 10000000000 49646493492249 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4449100741/10000000000 : ℝ), (-446697021/2000000000 : ℝ), (5776202371/10000000000 : ℝ)] ![(1779155453729/5000000000000 : ℝ), (2954079483/20000000000 : ℝ), (49646493492249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4449100741/10000000000 : ℝ)|^37 ≤ (1779155453729/5000000000000 : ℝ)^29
        have hw : |(4449100741/10000000000 : ℝ)|=(4449100741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-446697021/2000000000 : ℝ)|^37 ≤ (2954079483/20000000000 : ℝ)^29
        have hw : |(-446697021/2000000000 : ℝ)|=(446697021/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5776202371/10000000000 : ℝ)|^37 ≤ (49646493492249/100000000000000 : ℝ)^29
        have hw : |(5776202371/10000000000 : ℝ)|=(5776202371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s3_s3_16 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5108269909/10000000000 : ℝ)*x 0 + (18334101/31250000 : ℝ)*x 1 + (-1232029303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5108269909/10000000000 : ℝ)^37 ≤ (21221088549097/50000000000000 : ℝ)^29 := by
    have hnat : (5108269909 : ℕ)^37*50000000000000^29 ≤ 21221088549097^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5108269909 10000000000 21221088549097 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (18334101/31250000 : ℝ)^37 ≤ (10128673830927/20000000000000 : ℝ)^29 := by
    have hnat : (18334101 : ℕ)^37*20000000000000^29 ≤ 10128673830927^29*31250000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18334101 31250000 10128673830927 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1232029303/10000000000 : ℝ)^37 ≤ (6914453737661/100000000000000 : ℝ)^29 := by
    have hnat : (1232029303 : ℕ)^37*100000000000000^29 ≤ 6914453737661^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1232029303 10000000000 6914453737661 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5108269909/10000000000 : ℝ), (18334101/31250000 : ℝ), (-1232029303/10000000000 : ℝ)] ![(21221088549097/50000000000000 : ℝ), (10128673830927/20000000000000 : ℝ), (6914453737661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5108269909/10000000000 : ℝ)|^37 ≤ (21221088549097/50000000000000 : ℝ)^29
        have hw : |(5108269909/10000000000 : ℝ)|=(5108269909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(18334101/31250000 : ℝ)|^37 ≤ (10128673830927/20000000000000 : ℝ)^29
        have hw : |(18334101/31250000 : ℝ)|=(18334101/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1232029303/10000000000 : ℝ)|^37 ≤ (6914453737661/100000000000000 : ℝ)^29
        have hw : |(-1232029303/10000000000 : ℝ)|=(1232029303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s3_s3_20 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3231057157/5000000000 : ℝ)*x 0 + (2734943881/10000000000 : ℝ)*x 1 + (3223263373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3231057157/5000000000 : ℝ)^37 ≤ (28644034989677/50000000000000 : ℝ)^29 := by
    have hnat : (3231057157 : ℕ)^37*50000000000000^29 ≤ 28644034989677^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3231057157 5000000000 28644034989677 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2734943881/10000000000 : ℝ)^37 ≤ (2390748315249/12500000000000 : ℝ)^29 := by
    have hnat : (2734943881 : ℕ)^37*12500000000000^29 ≤ 2390748315249^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734943881 10000000000 2390748315249 12500000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3223263373/10000000000 : ℝ)^37 ≤ (23585943473847/100000000000000 : ℝ)^29 := by
    have hnat : (3223263373 : ℕ)^37*100000000000000^29 ≤ 23585943473847^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3223263373 10000000000 23585943473847 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3231057157/5000000000 : ℝ), (2734943881/10000000000 : ℝ), (3223263373/10000000000 : ℝ)] ![(28644034989677/50000000000000 : ℝ), (2390748315249/12500000000000 : ℝ), (23585943473847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3231057157/5000000000 : ℝ)|^37 ≤ (28644034989677/50000000000000 : ℝ)^29
        have hw : |(3231057157/5000000000 : ℝ)|=(3231057157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2734943881/10000000000 : ℝ)|^37 ≤ (2390748315249/12500000000000 : ℝ)^29
        have hw : |(2734943881/10000000000 : ℝ)|=(2734943881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3223263373/10000000000 : ℝ)|^37 ≤ (23585943473847/100000000000000 : ℝ)^29
        have hw : |(3223263373/10000000000 : ℝ)|=(3223263373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s3_s3_21 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1951330701/10000000000 : ℝ)*x 0 + (590845511/1250000000 : ℝ)*x 1 + (5728775997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1951330701/10000000000 : ℝ)^37 ≤ (3108136573907/25000000000000 : ℝ)^29 := by
    have hnat : (1951330701 : ℕ)^37*25000000000000^29 ≤ 3108136573907^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1951330701 10000000000 3108136573907 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (590845511/1250000000 : ℝ)^37 ≤ (38440449635621/100000000000000 : ℝ)^29 := by
    have hnat : (590845511 : ℕ)^37*100000000000000^29 ≤ 38440449635621^29*1250000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      590845511 1250000000 38440449635621 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5728775997/10000000000 : ℝ)^37 ≤ (61408755057/125000000000 : ℝ)^29 := by
    have hnat : (5728775997 : ℕ)^37*125000000000^29 ≤ 61408755057^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5728775997 10000000000 61408755057 125000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1951330701/10000000000 : ℝ), (590845511/1250000000 : ℝ), (5728775997/10000000000 : ℝ)] ![(3108136573907/25000000000000 : ℝ), (38440449635621/100000000000000 : ℝ), (61408755057/125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1951330701/10000000000 : ℝ)|^37 ≤ (3108136573907/25000000000000 : ℝ)^29
        have hw : |(-1951330701/10000000000 : ℝ)|=(1951330701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(590845511/1250000000 : ℝ)|^37 ≤ (38440449635621/100000000000000 : ℝ)^29
        have hw : |(590845511/1250000000 : ℝ)|=(590845511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5728775997/10000000000 : ℝ)|^37 ≤ (61408755057/125000000000 : ℝ)^29
        have hw : |(5728775997/10000000000 : ℝ)|=(5728775997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s3_s3_22 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5055303129/10000000000 : ℝ)*x 0 + (-1997835819/10000000000 : ℝ)*x 1 + (5376572469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5055303129/10000000000 : ℝ)^37 ≤ (20940753118573/50000000000000 : ℝ)^29 := by
    have hnat : (5055303129 : ℕ)^37*50000000000000^29 ≤ 20940753118573^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5055303129 10000000000 20940753118573 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1997835819/10000000000 : ℝ)^37 ≤ (12811818374301/100000000000000 : ℝ)^29 := by
    have hnat : (1997835819 : ℕ)^37*100000000000000^29 ≤ 12811818374301^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1997835819 10000000000 12811818374301 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5376572469/10000000000 : ℝ)^37 ≤ (45306675374813/100000000000000 : ℝ)^29 := by
    have hnat : (5376572469 : ℕ)^37*100000000000000^29 ≤ 45306675374813^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5376572469 10000000000 45306675374813 100000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5055303129/10000000000 : ℝ), (-1997835819/10000000000 : ℝ), (5376572469/10000000000 : ℝ)] ![(20940753118573/50000000000000 : ℝ), (12811818374301/100000000000000 : ℝ), (45306675374813/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5055303129/10000000000 : ℝ)|^37 ≤ (20940753118573/50000000000000 : ℝ)^29
        have hw : |(5055303129/10000000000 : ℝ)|=(5055303129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1997835819/10000000000 : ℝ)|^37 ≤ (12811818374301/100000000000000 : ℝ)^29
        have hw : |(-1997835819/10000000000 : ℝ)|=(1997835819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5376572469/10000000000 : ℝ)|^37 ≤ (45306675374813/100000000000000 : ℝ)^29
        have hw : |(5376572469/10000000000 : ℝ)|=(5376572469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s3_s3_23 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (887380087/2000000000 : ℝ)*x 0 + (3160715787/5000000000 : ℝ)*x 1 + (-746800737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (887380087/2000000000 : ℝ)^37 ≤ (554041607159/1562500000000 : ℝ)^29 := by
    have hnat : (887380087 : ℕ)^37*1562500000000^29 ≤ 554041607159^29*2000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887380087 2000000000 554041607159 1562500000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3160715787/5000000000 : ℝ)^37 ≤ (13925409830751/25000000000000 : ℝ)^29 := by
    have hnat : (3160715787 : ℕ)^37*25000000000000^29 ≤ 13925409830751^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3160715787 5000000000 13925409830751 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (746800737/5000000000 : ℝ)^37 ≤ (276240556551/3125000000000 : ℝ)^29 := by
    have hnat : (746800737 : ℕ)^37*3125000000000^29 ≤ 276240556551^29*5000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      746800737 5000000000 276240556551 3125000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(887380087/2000000000 : ℝ), (3160715787/5000000000 : ℝ), (-746800737/5000000000 : ℝ)] ![(554041607159/1562500000000 : ℝ), (13925409830751/25000000000000 : ℝ), (276240556551/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(887380087/2000000000 : ℝ)|^37 ≤ (554041607159/1562500000000 : ℝ)^29
        have hw : |(887380087/2000000000 : ℝ)|=(887380087/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3160715787/5000000000 : ℝ)|^37 ≤ (13925409830751/25000000000000 : ℝ)^29
        have hw : |(3160715787/5000000000 : ℝ)|=(3160715787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-746800737/5000000000 : ℝ)|^37 ≤ (276240556551/3125000000000 : ℝ)^29
        have hw : |(-746800737/5000000000 : ℝ)|=(746800737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c313061_s3_s3_27 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1637582111/2500000000 : ℝ)*x 0 + (2720777017/10000000000 : ℝ)*x 1 + (782334631/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1637582111/2500000000 : ℝ)^37 ≤ (14571928701943/25000000000000 : ℝ)^29 := by
    have hnat : (1637582111 : ℕ)^37*25000000000000^29 ≤ 14571928701943^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1637582111 2500000000 14571928701943 25000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2720777017/10000000000 : ℝ)^37 ≤ (9499837628553/50000000000000 : ℝ)^29 := by
    have hnat : (2720777017 : ℕ)^37*50000000000000^29 ≤ 9499837628553^29*10000000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2720777017 10000000000 9499837628553 50000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (782334631/2500000000 : ℝ)^37 ≤ (4542521984521/20000000000000 : ℝ)^29 := by
    have hnat : (782334631 : ℕ)^37*20000000000000^29 ≤ 4542521984521^29*2500000000^37 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      782334631 2500000000 4542521984521 20000000000000 37 29 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (37/8 : ℝ)) 37 29 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1637582111/2500000000 : ℝ), (2720777017/10000000000 : ℝ), (782334631/2500000000 : ℝ)] ![(14571928701943/25000000000000 : ℝ), (9499837628553/50000000000000 : ℝ), (4542521984521/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1637582111/2500000000 : ℝ)|^37 ≤ (14571928701943/25000000000000 : ℝ)^29
        have hw : |(1637582111/2500000000 : ℝ)|=(1637582111/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2720777017/10000000000 : ℝ)|^37 ≤ (9499837628553/50000000000000 : ℝ)^29
        have hw : |(2720777017/10000000000 : ℝ)|=(2720777017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(782334631/2500000000 : ℝ)|^37 ≤ (4542521984521/20000000000000 : ℝ)^29
        have hw : |(782334631/2500000000 : ℝ)|=(782334631/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c313061_s3 (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((38159/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38159/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22221/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22221/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40353/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(40353/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4599/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4599/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23283/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(23283/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5367/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5367/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78599/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78599/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78599/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78599/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78599/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (38159/100000 : ℝ) ^ (73/16 : ℝ) ≤ (1233207746337590729/100000000000000000000 : ℝ) := by
    have hpowers : (38159/100000 : ℝ)^73 ≤ (1233207746337590729/100000000000000000000 : ℝ)^16 := by
      have hnat : (38159 : ℕ)^73*100000000000000000000^16 ≤ 1233207746337590729^16*100000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        38159 100000 1233207746337590729 100000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (38159/100000 : ℝ)) (X := (1233207746337590729/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s3_corner0a : (101233207746337590729/100000000000000000000 : ℝ) ≤ (5013450010586943/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (101233207746337590729/100000000000000000000 : ℝ)^16 ≤ (5013450010586943/5000000000000000 : ℝ)^73 := by
      have hnat : (101233207746337590729 : ℕ)^16*5000000000000000^73 ≤ 5013450010586943^73*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101233207746337590729 100000000000000000000 5013450010586943 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5013450010586943/5000000000000000 : ℝ)) (X := (101233207746337590729/100000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s3_corner0b : (51233207746337590729/50000000000000000000 : ℝ) ≤ (10053545377564541/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (51233207746337590729/50000000000000000000 : ℝ)^16 ≤ (10053545377564541/10000000000000000 : ℝ)^73 := by
      have hnat : (51233207746337590729 : ℕ)^16*10000000000000000^73 ≤ 10053545377564541^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51233207746337590729 50000000000000000000 10053545377564541 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10053545377564541/10000000000000000 : ℝ)) (X := (51233207746337590729/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(13450010586943/1907950000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(5329071278131/763180000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (38159/100000 : ℝ)) (alpha := (13450010586943/1907950000000000 : ℝ)) (beta := (5329071278131/763180000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (38159/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(13450010586943/1907950000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(5329071278131/763180000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (22221/50000 : ℝ) ^ (73/16 : ℝ) ≤ (309006980544772059/12500000000000000000 : ℝ) := by
    have hpowers : (22221/50000 : ℝ)^73 ≤ (309006980544772059/12500000000000000000 : ℝ)^16 := by
      have hnat : (22221 : ℕ)^73*12500000000000000000^16 ≤ 309006980544772059^16*50000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        22221 50000 309006980544772059 12500000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (22221/50000 : ℝ)) (X := (309006980544772059/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s3_corner1a : (12809006980544772059/12500000000000000000 : ℝ) ≤ (5026833334714479/5000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (12809006980544772059/12500000000000000000 : ℝ)^16 ≤ (5026833334714479/5000000000000000 : ℝ)^73 := by
      have hnat : (12809006980544772059 : ℕ)^16*5000000000000000^73 ≤ 5026833334714479^73*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12809006980544772059 12500000000000000000 5026833334714479 5000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5026833334714479/5000000000000000 : ℝ)) (X := (12809006980544772059/12500000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s3_corner1b : (6559006980544772059/6250000000000000000 : ℝ) ≤ (10106331763606837/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (6559006980544772059/6250000000000000000 : ℝ)^16 ≤ (10106331763606837/10000000000000000 : ℝ)^73 := by
      have hnat : (6559006980544772059 : ℕ)^16*10000000000000000^73 ≤ 10106331763606837^73*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6559006980544772059 6250000000000000000 10106331763606837 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10106331763606837/10000000000000000 : ℝ)) (X := (6559006980544772059/6250000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(26833334714479/2222100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(52665094177879/4444200000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (22221/50000 : ℝ)) (alpha := (26833334714479/2222100000000000 : ℝ)) (beta := (52665094177879/4444200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (22221/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(26833334714479/2222100000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(52665094177879/4444200000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (40353/100000 : ℝ) ^ (73/16 : ℝ) ≤ (1591506668064861321/100000000000000000000 : ℝ) := by
    have hpowers : (40353/100000 : ℝ)^73 ≤ (1591506668064861321/100000000000000000000 : ℝ)^16 := by
      have hnat : (40353 : ℕ)^73*100000000000000000000^16 ≤ 1591506668064861321^16*100000^73 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40353 100000 1591506668064861321 100000000000000000000 73 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (40353/100000 : ℝ)) (X := (1591506668064861321/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s3_corner2a : (101591506668064861321/100000000000000000000 : ℝ) ≤ (10034667624645779/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (101591506668064861321/100000000000000000000 : ℝ)^16 ≤ (10034667624645779/10000000000000000 : ℝ)^73 := by
      have hnat : (101591506668064861321 : ℕ)^16*10000000000000000^73 ≤ 10034667624645779^73*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101591506668064861321 100000000000000000000 10034667624645779 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10034667624645779/10000000000000000 : ℝ)) (X := (101591506668064861321/100000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have s3_corner2b : (51591506668064861321/50000000000000000000 : ℝ) ≤ (10068913748667973/10000000000000000 : ℝ) ^ (73/16 : ℝ) := by
    have hpowers : (51591506668064861321/50000000000000000000 : ℝ)^16 ≤ (10068913748667973/10000000000000000 : ℝ)^73 := by
      have hnat : (51591506668064861321 : ℕ)^16*10000000000000000^73 ≤ 10068913748667973^73*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51591506668064861321 50000000000000000000 10068913748667973 10000000000000000 16 73 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10068913748667973/10000000000000000 : ℝ)) (X := (51591506668064861321/50000000000000000000 : ℝ)) (by norm_num) 73 16 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(34667624645779/4035300000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(17123062011097/2017650000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (73/16 : ℝ)) (rho := (40353/100000 : ℝ)) (alpha := (34667624645779/4035300000000000 : ℝ)) (beta := (17123062011097/2017650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (40353/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(34667624645779/4035300000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(17123062011097/2017650000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-291942911/1250000000 : ℝ)*X 0 0+(895653853/2000000000 : ℝ)*X 0 1+(1133949817/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((4664095561/10000000000 : ℝ)*X 1 0+(-297525861/1250000000 : ℝ)*X 1 1+(2729243209/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((293049027/625000000 : ℝ)*X 2 0+(605651073/1000000000 : ℝ)*X 2 1+(-38568721/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((1484298293/2500000000 : ℝ)*X 0 0+(12012387/40000000 : ℝ)*X 0 1+(3586781343/10000000000 : ℝ)*X 0 2+(1484298293/2500000000 : ℝ)*X 1 0+(12012387/40000000 : ℝ)*X 1 1+(3586781343/10000000000 : ℝ)*X 1 2+(1484298293/2500000000 : ℝ)*X 2 0+(12012387/40000000 : ℝ)*X 2 1+(3586781343/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-18347821/78125000 : ℝ)*X 0 0+(4313631187/10000000000 : ℝ)*X 0 1+(1453140631/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((1136254717/2500000000 : ℝ)*X 1 0+(-2113856259/10000000000 : ℝ)*X 1 1+(5778040269/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((285608279/625000000 : ℝ)*X 2 0+(1274565167/2000000000 : ℝ)*X 2 1+(-1230191923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((5962629373/10000000000 : ℝ)*X 0 0+(826994813/2500000000 : ℝ)*X 0 1+(1629517013/5000000000 : ℝ)*X 0 2+(5962629373/10000000000 : ℝ)*X 1 0+(826994813/2500000000 : ℝ)*X 1 1+(1629517013/5000000000 : ℝ)*X 1 2+(5962629373/10000000000 : ℝ)*X 2 0+(826994813/2500000000 : ℝ)*X 2 1+(1629517013/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-961538807/5000000000 : ℝ)*X 0 0+(2322137279/5000000000 : ℝ)*X 0 1+(2913765321/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((4449100741/10000000000 : ℝ)*X 1 0+(-446697021/2000000000 : ℝ)*X 1 1+(5776202371/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((5108269909/10000000000 : ℝ)*X 2 0+(18334101/31250000 : ℝ)*X 2 1+(-1232029303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((3231057157/5000000000 : ℝ)*X 0 0+(2734943881/10000000000 : ℝ)*X 0 1+(3223263373/10000000000 : ℝ)*X 0 2+(3231057157/5000000000 : ℝ)*X 1 0+(2734943881/10000000000 : ℝ)*X 1 1+(3223263373/10000000000 : ℝ)*X 1 2+(3231057157/5000000000 : ℝ)*X 2 0+(2734943881/10000000000 : ℝ)*X 2 1+(3223263373/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-1951330701/10000000000 : ℝ)*X 0 0+(590845511/1250000000 : ℝ)*X 0 1+(5728775997/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((5055303129/10000000000 : ℝ)*X 1 0+(-1997835819/10000000000 : ℝ)*X 1 1+(5376572469/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((887380087/2000000000 : ℝ)*X 2 0+(3160715787/5000000000 : ℝ)*X 2 1+(-746800737/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((1637582111/2500000000 : ℝ)*X 0 0+(2720777017/10000000000 : ℝ)*X 0 1+(782334631/2500000000 : ℝ)*X 0 2+(1637582111/2500000000 : ℝ)*X 1 0+(2720777017/10000000000 : ℝ)*X 1 1+(782334631/2500000000 : ℝ)*X 1 2+(1637582111/2500000000 : ℝ)*X 2 0+(2720777017/10000000000 : ℝ)*X 2 1+(782334631/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c313061_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((4599/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4599/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (23761372536164336777444023/2490788925000000000000000000000 : ℝ) := by norm_num
    linear_combination (66357/100000000000 : ℝ)*(base50) + (2170198210167/1000000000000 : ℝ)*(base59) + (1442012535829/125000000000 : ℝ)*(major_s3_0) + (1442012535829/125000000000 : ℝ)*(major_s3_1) + (1442012535829/125000000000 : ℝ)*(major_s3_2) + (31823391/200000000000 : ℝ)*(sp_s3_0) + (2940299/62500000000 : ℝ)*(sp_s3_1) + (52252033/500000000000 : ℝ)*(sp_s3_6) + (8132778687127/500000000000 : ℝ)*(sp_s3_7) + (3253061637869/200000000000 : ℝ)*(sp_s3_8) + (325310912851/20000000000 : ℝ)*(sp_s3_9) + (6806376398087/1000000000000 : ℝ)*(sp_s3_13) + (9031427/25000000000 : ℝ)*(sp_s3_15) + (170848659/1000000000000 : ℝ)*(sp_s3_23) + (6806480902153/1000000000000 : ℝ)*(f.failure) + (16265716491209/1000000000000 : ℝ)*(f.sum) + (5310280382812474993/14944733550000000000000000000000 : ℝ)*base62 + (763519488489991/2017650000000000000000000000 : ℝ)*base65 + (276736244044427/1111050000000000000000000000 : ℝ)*base67 + (236779613204591/2017650000000000000000000000 : ℝ)*base68 + (39976666125036821297/76991506350000000000000000000000 : ℝ)*base71 + (52770797396027/381590000000000000000000000 : ℝ)*base72 + (35050653989111/69440625000000000000000000 : ℝ)*base74 + (76544223082831/476987500000000000000000000 : ℝ)*base76 + (8509302292589540969/21198278475000000000000000000000 : ℝ)*base79 + (5511/100000000000000000 : ℝ)*base87 + (5511/100000000000000000 : ℝ)*base89 + (5511/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23283/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(23283/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (51803660307371060029465369/5132767090000000000000000000000 : ℝ) := by norm_num
    linear_combination (1880279/1000000000000 : ℝ)*(base39) + (5299784757/200000000000 : ℝ)*(base40) + (345390750031/200000000000 : ℝ)*(base59) + (1117876175761/100000000000 : ℝ)*(major_s3_0) + (1117876175761/100000000000 : ℝ)*(major_s3_1) + (1117876175761/100000000000 : ℝ)*(major_s3_2) + (128959089/500000000000 : ℝ)*(sp_s3_1) + (73416411/200000000000 : ℝ)*(sp_s3_2) + (41797997/500000000000 : ℝ)*(sp_s3_6) + (82785451/200000000000 : ℝ)*(sp_s3_7) + (15761460682991/1000000000000 : ℝ)*(sp_s3_14) + (3940404173017/250000000000 : ℝ)*(sp_s3_15) + (15761507528191/1000000000000 : ℝ)*(sp_s3_16) + (1648890486183/250000000000 : ℝ)*(sp_s3_20) + (3297822770363/500000000000 : ℝ)*(f.failure) + (7880937305123/500000000000 : ℝ)*(f.sum) + (1034703509591527/37361833875000000000000000000 : ℝ)*base63 + (215566733056049/403530000000000000000000000 : ℝ)*base64 + (145232341815521/444420000000000000000000000 : ℝ)*base66 + (117873746920067/403530000000000000000000000 : ℝ)*base68 + (1366549818221929711/3849575317500000000000000000000 : ℝ)*base70 + (21758470864707/76318000000000000000000000 : ℝ)*base72 + (1024686617009/3472031250000000000000000 : ℝ)*base74 + (43468979359253/95397500000000000000000000 : ℝ)*base76 + (110323820809629641/16958622780000000000000000000000 : ℝ)*base79 + (13781/50000000000000000 : ℝ)*base87 + (13781/50000000000000000 : ℝ)*base89 + (13781/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5367/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5367/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (55066216405474332133419705811/4224267315070000000000000000000000 : ℝ) := by norm_num
    linear_combination (493979707307/1000000000000 : ℝ)*(base40) + (3470471/1000000000000 : ℝ)*(base50) + (1814361467593/1000000000000 : ℝ)*(base59) + (551415110877/50000000000 : ℝ)*(major_s3_0) + (551415110877/50000000000 : ℝ)*(major_s3_1) + (551415110877/50000000000 : ℝ)*(major_s3_2) + (677819443/1000000000000 : ℝ)*(sp_s3_0) + (337866227/500000000000 : ℝ)*(sp_s3_1) + (154109273/1000000000000 : ℝ)*(sp_s3_2) + (11075679/100000000000 : ℝ)*(sp_s3_9) + (15549050228573/1000000000000 : ℝ)*(sp_s3_21) + (7774526157781/500000000000 : ℝ)*(sp_s3_22) + (15549463181953/1000000000000 : ℝ)*(sp_s3_23) + (813359005229/125000000000 : ℝ)*(sp_s3_27) + (813359005229/125000000000 : ℝ)*(f.failure) + (971858003001/62500000000 : ℝ)*(f.sum) + (150395979861031723/332105190000000000000000000000 : ℝ)*base63 + (16707011773881/26902000000000000000000000 : ℝ)*base64 + (11418102054989/24690000000000000000000000 : ℝ)*base66 + (6480284713739/67255000000000000000000000 : ℝ)*base68 + (58054110409444101/513276709000000000000000000000 : ℝ)*base70 + (40635017674423/95397500000000000000000000 : ℝ)*base72 + (4341040583303/24690000000000000000000000 : ℝ)*base75 + (1199650141919/38159000000000000000000000 : ℝ)*base77 + (403794574370177713/942145710000000000000000000000 : ℝ)*base78 + (2477/12500000000000000 : ℝ)*base86 + (2477/12500000000000000 : ℝ)*base88 + (2477/12500000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (73/16 : ℝ) ≤ p) (hpb : p ≤ (37/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (169487/100000 : ℝ) (176973/100000 : ℝ) (78599/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev2 : (0 : ℝ) ≤ ((38159/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(38159/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(22221/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(22221/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40353/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(40353/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((4599/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(4599/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(23283/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(23283/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5367/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(5367/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c313061_s3 p hpa hpb X hX hprev2

#print axioms solution
