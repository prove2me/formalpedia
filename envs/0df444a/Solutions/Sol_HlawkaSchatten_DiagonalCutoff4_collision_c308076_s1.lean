-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308076_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:39:41.422818+00:00
-- url     : https://prove2.me/submissions/173bc36c-bafd-47ff-9df7-fcd716ef3284

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
theorem collision_support_c308076_s1_s1_0 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1391738329/10000000000 : ℝ)*x 0 + (-6372047997/10000000000 : ℝ)*x 1 + (1157852759/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1391738329/10000000000 : ℝ)^69 ≤ (3836886387819/50000000000000 : ℝ)^53 := by
    have hnat : (1391738329 : ℕ)^69*50000000000000^53 ≤ 3836886387819^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1391738329 10000000000 3836886387819 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6372047997/10000000000 : ℝ)^69 ≤ (55615195106487/100000000000000 : ℝ)^53 := by
    have hnat : (6372047997 : ℕ)^69*100000000000000^53 ≤ 55615195106487^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6372047997 10000000000 55615195106487 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1157852759/2500000000 : ℝ)^69 ≤ (18355516048109/50000000000000 : ℝ)^53 := by
    have hnat : (1157852759 : ℕ)^69*50000000000000^53 ≤ 18355516048109^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1157852759 2500000000 18355516048109 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1391738329/10000000000 : ℝ), (-6372047997/10000000000 : ℝ), (1157852759/2500000000 : ℝ)] ![(3836886387819/50000000000000 : ℝ), (55615195106487/100000000000000 : ℝ), (18355516048109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1391738329/10000000000 : ℝ)|^69 ≤ (3836886387819/50000000000000 : ℝ)^53
        have hw : |(-1391738329/10000000000 : ℝ)|=(1391738329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6372047997/10000000000 : ℝ)|^69 ≤ (55615195106487/100000000000000 : ℝ)^53
        have hw : |(-6372047997/10000000000 : ℝ)|=(6372047997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1157852759/2500000000 : ℝ)|^69 ≤ (18355516048109/50000000000000 : ℝ)^53
        have hw : |(1157852759/2500000000 : ℝ)|=(1157852759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308076_s1_s1_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6522540973/10000000000 : ℝ)*x 0 + (1636733859/5000000000 : ℝ)*x 1 + (2826583269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6522540973/10000000000 : ℝ)^69 ≤ (5733128866351/10000000000000 : ℝ)^53 := by
    have hnat : (6522540973 : ℕ)^69*10000000000000^53 ≤ 5733128866351^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6522540973 10000000000 5733128866351 10000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1636733859/5000000000 : ℝ)^69 ≤ (11683296712801/50000000000000 : ℝ)^53 := by
    have hnat : (1636733859 : ℕ)^69*50000000000000^53 ≤ 11683296712801^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1636733859 5000000000 11683296712801 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2826583269/10000000000 : ℝ)^69 ≤ (965105895029/5000000000000 : ℝ)^53 := by
    have hnat : (2826583269 : ℕ)^69*5000000000000^53 ≤ 965105895029^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2826583269 10000000000 965105895029 5000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6522540973/10000000000 : ℝ), (1636733859/5000000000 : ℝ), (2826583269/10000000000 : ℝ)] ![(5733128866351/10000000000000 : ℝ), (11683296712801/50000000000000 : ℝ), (965105895029/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6522540973/10000000000 : ℝ)|^69 ≤ (5733128866351/10000000000000 : ℝ)^53
        have hw : |(6522540973/10000000000 : ℝ)|=(6522540973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1636733859/5000000000 : ℝ)|^69 ≤ (11683296712801/50000000000000 : ℝ)^53
        have hw : |(1636733859/5000000000 : ℝ)|=(1636733859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2826583269/10000000000 : ℝ)|^69 ≤ (965105895029/5000000000000 : ℝ)^53
        have hw : |(2826583269/10000000000 : ℝ)|=(2826583269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308076_s1_s1_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-563753649/5000000000 : ℝ)*x 0 + (-1903895433/2500000000 : ℝ)*x 1 + (3343761893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (563753649/5000000000 : ℝ)^69 ≤ (145850097819/2500000000000 : ℝ)^53 := by
    have hnat : (563753649 : ℕ)^69*2500000000000^53 ≤ 145850097819^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      563753649 5000000000 145850097819 2500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1903895433/2500000000 : ℝ)^69 ≤ (35072022497819/50000000000000 : ℝ)^53 := by
    have hnat : (1903895433 : ℕ)^69*50000000000000^53 ≤ 35072022497819^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1903895433 2500000000 35072022497819 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3343761893/10000000000 : ℝ)^69 ≤ (12010975537287/50000000000000 : ℝ)^53 := by
    have hnat : (3343761893 : ℕ)^69*50000000000000^53 ≤ 12010975537287^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3343761893 10000000000 12010975537287 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-563753649/5000000000 : ℝ), (-1903895433/2500000000 : ℝ), (3343761893/10000000000 : ℝ)] ![(145850097819/2500000000000 : ℝ), (35072022497819/50000000000000 : ℝ), (12010975537287/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-563753649/5000000000 : ℝ)|^69 ≤ (145850097819/2500000000000 : ℝ)^53
        have hw : |(-563753649/5000000000 : ℝ)|=(563753649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1903895433/2500000000 : ℝ)|^69 ≤ (35072022497819/50000000000000 : ℝ)^53
        have hw : |(-1903895433/2500000000 : ℝ)|=(1903895433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3343761893/10000000000 : ℝ)|^69 ≤ (12010975537287/50000000000000 : ℝ)^53
        have hw : |(3343761893/10000000000 : ℝ)|=(3343761893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308076_s1_s1_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2612901107/5000000000 : ℝ)*x 0 + (4664521947/10000000000 : ℝ)*x 1 + (2835222/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612901107/5000000000 : ℝ)^69 ≤ (21480138465187/50000000000000 : ℝ)^53 := by
    have hnat : (2612901107 : ℕ)^69*50000000000000^53 ≤ 21480138465187^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612901107 5000000000 21480138465187 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4664521947/10000000000 : ℝ)^69 ≤ (1157908954657/3125000000000 : ℝ)^53 := by
    have hnat : (4664521947 : ℕ)^69*3125000000000^53 ≤ 1157908954657^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4664521947 10000000000 1157908954657 3125000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2835222/9765625 : ℝ)^69 ≤ (249832956339/1250000000000 : ℝ)^53 := by
    have hnat : (2835222 : ℕ)^69*1250000000000^53 ≤ 249832956339^53*9765625^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2835222 9765625 249832956339 1250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612901107/5000000000 : ℝ), (4664521947/10000000000 : ℝ), (2835222/9765625 : ℝ)] ![(21480138465187/50000000000000 : ℝ), (1157908954657/3125000000000 : ℝ), (249832956339/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612901107/5000000000 : ℝ)|^69 ≤ (21480138465187/50000000000000 : ℝ)^53
        have hw : |(2612901107/5000000000 : ℝ)|=(2612901107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4664521947/10000000000 : ℝ)|^69 ≤ (1157908954657/3125000000000 : ℝ)^53
        have hw : |(4664521947/10000000000 : ℝ)|=(4664521947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2835222/9765625 : ℝ)|^69 ≤ (249832956339/1250000000000 : ℝ)^53
        have hw : |(2835222/9765625 : ℝ)|=(2835222/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308076_s1_s1_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (27819373/50000000 : ℝ)*x 0 + (-5430378499/10000000000 : ℝ)*x 1 + (-733890859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (27819373/50000000 : ℝ)^69 ≤ (46613328230109/100000000000000 : ℝ)^53 := by
    have hnat : (27819373 : ℕ)^69*100000000000000^53 ≤ 46613328230109^53*50000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27819373 50000000 46613328230109 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5430378499/10000000000 : ℝ)^69 ≤ (22581293483057/50000000000000 : ℝ)^53 := by
    have hnat : (5430378499 : ℕ)^69*50000000000000^53 ≤ 22581293483057^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430378499 10000000000 22581293483057 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (733890859/5000000000 : ℝ)^69 ≤ (205602119827/2500000000000 : ℝ)^53 := by
    have hnat : (733890859 : ℕ)^69*2500000000000^53 ≤ 205602119827^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      733890859 5000000000 205602119827 2500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(27819373/50000000 : ℝ), (-5430378499/10000000000 : ℝ), (-733890859/5000000000 : ℝ)] ![(46613328230109/100000000000000 : ℝ), (22581293483057/50000000000000 : ℝ), (205602119827/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(27819373/50000000 : ℝ)|^69 ≤ (46613328230109/100000000000000 : ℝ)^53
        have hw : |(27819373/50000000 : ℝ)|=(27819373/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5430378499/10000000000 : ℝ)|^69 ≤ (22581293483057/50000000000000 : ℝ)^53
        have hw : |(-5430378499/10000000000 : ℝ)|=(5430378499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-733890859/5000000000 : ℝ)|^69 ≤ (205602119827/2500000000000 : ℝ)^53
        have hw : |(-733890859/5000000000 : ℝ)|=(733890859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308076_s1_s1_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3150632541/10000000000 : ℝ)*x 0 + (38245183/5000000000 : ℝ)*x 1 + (1645886149/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3150632541/10000000000 : ℝ)^69 ≤ (444631939977/2000000000000 : ℝ)^53 := by
    have hnat : (3150632541 : ℕ)^69*2000000000000^53 ≤ 444631939977^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3150632541 10000000000 444631939977 2000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (38245183/5000000000 : ℝ)^69 ≤ (43917294169/25000000000000 : ℝ)^53 := by
    have hnat : (38245183 : ℕ)^69*25000000000000^53 ≤ 43917294169^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38245183 5000000000 43917294169 25000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1645886149/2000000000 : ℝ)^69 ≤ (77592733812437/100000000000000 : ℝ)^53 := by
    have hnat : (1645886149 : ℕ)^69*100000000000000^53 ≤ 77592733812437^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1645886149 2000000000 77592733812437 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3150632541/10000000000 : ℝ), (38245183/5000000000 : ℝ), (1645886149/2000000000 : ℝ)] ![(444631939977/2000000000000 : ℝ), (43917294169/25000000000000 : ℝ), (77592733812437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3150632541/10000000000 : ℝ)|^69 ≤ (444631939977/2000000000000 : ℝ)^53
        have hw : |(3150632541/10000000000 : ℝ)|=(3150632541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(38245183/5000000000 : ℝ)|^69 ≤ (43917294169/25000000000000 : ℝ)^53
        have hw : |(38245183/5000000000 : ℝ)|=(38245183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1645886149/2000000000 : ℝ)|^69 ≤ (77592733812437/100000000000000 : ℝ)^53
        have hw : |(1645886149/2000000000 : ℝ)|=(1645886149/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308076_s1_s1_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1142374289/10000000000 : ℝ)*x 0 + (-4387226713/10000000000 : ℝ)*x 1 + (3370952313/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1142374289/10000000000 : ℝ)^69 ≤ (5934350946141/100000000000000 : ℝ)^53 := by
    have hnat : (1142374289 : ℕ)^69*100000000000000^53 ≤ 5934350946141^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142374289 10000000000 5934350946141 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4387226713/10000000000 : ℝ)^69 ≤ (34211489871673/100000000000000 : ℝ)^53 := by
    have hnat : (4387226713 : ℕ)^69*100000000000000^53 ≤ 34211489871673^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4387226713 10000000000 34211489871673 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3370952313/5000000000 : ℝ)^69 ≤ (11970831832471/20000000000000 : ℝ)^53 := by
    have hnat : (3370952313 : ℕ)^69*20000000000000^53 ≤ 11970831832471^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3370952313 5000000000 11970831832471 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1142374289/10000000000 : ℝ), (-4387226713/10000000000 : ℝ), (3370952313/5000000000 : ℝ)] ![(5934350946141/100000000000000 : ℝ), (34211489871673/100000000000000 : ℝ), (11970831832471/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1142374289/10000000000 : ℝ)|^69 ≤ (5934350946141/100000000000000 : ℝ)^53
        have hw : |(-1142374289/10000000000 : ℝ)|=(1142374289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4387226713/10000000000 : ℝ)|^69 ≤ (34211489871673/100000000000000 : ℝ)^53
        have hw : |(-4387226713/10000000000 : ℝ)|=(4387226713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3370952313/5000000000 : ℝ)|^69 ≤ (11970831832471/20000000000000 : ℝ)^53
        have hw : |(3370952313/5000000000 : ℝ)|=(3370952313/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308076_s1_s1_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1546551507/2000000000 : ℝ)*x 0 + (1242849327/5000000000 : ℝ)*x 1 + (197698733/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1546551507/2000000000 : ℝ)^69 ≤ (8944046200081/12500000000000 : ℝ)^53 := by
    have hnat : (1546551507 : ℕ)^69*12500000000000^53 ≤ 8944046200081^53*2000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1546551507 2000000000 8944046200081 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1242849327/5000000000 : ℝ)^69 ≤ (16328352108517/100000000000000 : ℝ)^53 := by
    have hnat : (1242849327 : ℕ)^69*100000000000000^53 ≤ 16328352108517^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1242849327 5000000000 16328352108517 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (197698733/1000000000 : ℝ)^69 ≤ (12119278267277/100000000000000 : ℝ)^53 := by
    have hnat : (197698733 : ℕ)^69*100000000000000^53 ≤ 12119278267277^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197698733 1000000000 12119278267277 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1546551507/2000000000 : ℝ), (1242849327/5000000000 : ℝ), (197698733/1000000000 : ℝ)] ![(8944046200081/12500000000000 : ℝ), (16328352108517/100000000000000 : ℝ), (12119278267277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1546551507/2000000000 : ℝ)|^69 ≤ (8944046200081/12500000000000 : ℝ)^53
        have hw : |(1546551507/2000000000 : ℝ)|=(1546551507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1242849327/5000000000 : ℝ)|^69 ≤ (16328352108517/100000000000000 : ℝ)^53
        have hw : |(1242849327/5000000000 : ℝ)|=(1242849327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(197698733/1000000000 : ℝ)|^69 ≤ (12119278267277/100000000000000 : ℝ)^53
        have hw : |(197698733/1000000000 : ℝ)|=(197698733/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308076_s1_s1_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4906575679/10000000000 : ℝ)*x 0 + (-5754677697/10000000000 : ℝ)*x 1 + (-1926661469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4906575679/10000000000 : ℝ)^69 ≤ (7915140187667/20000000000000 : ℝ)^53 := by
    have hnat : (4906575679 : ℕ)^69*20000000000000^53 ≤ 7915140187667^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4906575679 10000000000 7915140187667 20000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5754677697/10000000000 : ℝ)^69 ≤ (48705108596639/100000000000000 : ℝ)^53 := by
    have hnat : (5754677697 : ℕ)^69*100000000000000^53 ≤ 48705108596639^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5754677697 10000000000 48705108596639 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1926661469/10000000000 : ℝ)^69 ≤ (5859595223197/50000000000000 : ℝ)^53 := by
    have hnat : (1926661469 : ℕ)^69*50000000000000^53 ≤ 5859595223197^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1926661469 10000000000 5859595223197 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4906575679/10000000000 : ℝ), (-5754677697/10000000000 : ℝ), (-1926661469/10000000000 : ℝ)] ![(7915140187667/20000000000000 : ℝ), (48705108596639/100000000000000 : ℝ), (5859595223197/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4906575679/10000000000 : ℝ)|^69 ≤ (7915140187667/20000000000000 : ℝ)^53
        have hw : |(4906575679/10000000000 : ℝ)|=(4906575679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5754677697/10000000000 : ℝ)|^69 ≤ (48705108596639/100000000000000 : ℝ)^53
        have hw : |(-5754677697/10000000000 : ℝ)|=(5754677697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1926661469/10000000000 : ℝ)|^69 ≤ (5859595223197/50000000000000 : ℝ)^53
        have hw : |(-1926661469/10000000000 : ℝ)|=(1926661469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308076_s1_s1_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1928281861/10000000000 : ℝ)*x 0 + (-76013/2500000000 : ℝ)*x 1 + (9085943937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1928281861/10000000000 : ℝ)^69 ≤ (733251488367/6250000000000 : ℝ)^53 := by
    have hnat : (1928281861 : ℕ)^69*6250000000000^53 ≤ 733251488367^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1928281861 10000000000 733251488367 6250000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (76013/2500000000 : ℝ)^69 ≤ (65808121/50000000000000 : ℝ)^53 := by
    have hnat : (76013 : ℕ)^69*50000000000000^53 ≤ 65808121^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76013 2500000000 65808121 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9085943937/10000000000 : ℝ)^69 ≤ (88267844554453/100000000000000 : ℝ)^53 := by
    have hnat : (9085943937 : ℕ)^69*100000000000000^53 ≤ 88267844554453^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9085943937 10000000000 88267844554453 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1928281861/10000000000 : ℝ), (-76013/2500000000 : ℝ), (9085943937/10000000000 : ℝ)] ![(733251488367/6250000000000 : ℝ), (65808121/50000000000000 : ℝ), (88267844554453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1928281861/10000000000 : ℝ)|^69 ≤ (733251488367/6250000000000 : ℝ)^53
        have hw : |(1928281861/10000000000 : ℝ)|=(1928281861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-76013/2500000000 : ℝ)|^69 ≤ (65808121/50000000000000 : ℝ)^53
        have hw : |(-76013/2500000000 : ℝ)|=(76013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9085943937/10000000000 : ℝ)|^69 ≤ (88267844554453/100000000000000 : ℝ)^53
        have hw : |(9085943937/10000000000 : ℝ)|=(9085943937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308076_s1_s1_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-258408889/5000000000 : ℝ)*x 0 + (-768518847/1000000000 : ℝ)*x 1 + (3648139889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258408889/5000000000 : ℝ)^69 ≤ (2113056028477/100000000000000 : ℝ)^53 := by
    have hnat : (258408889 : ℕ)^69*100000000000000^53 ≤ 2113056028477^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258408889 5000000000 2113056028477 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (768518847/1000000000 : ℝ)^69 ≤ (35489929564661/50000000000000 : ℝ)^53 := by
    have hnat : (768518847 : ℕ)^69*50000000000000^53 ≤ 35489929564661^53*1000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      768518847 1000000000 35489929564661 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3648139889/10000000000 : ℝ)^69 ≤ (13453542412069/50000000000000 : ℝ)^53 := by
    have hnat : (3648139889 : ℕ)^69*50000000000000^53 ≤ 13453542412069^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3648139889 10000000000 13453542412069 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-258408889/5000000000 : ℝ), (-768518847/1000000000 : ℝ), (3648139889/10000000000 : ℝ)] ![(2113056028477/100000000000000 : ℝ), (35489929564661/50000000000000 : ℝ), (13453542412069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-258408889/5000000000 : ℝ)|^69 ≤ (2113056028477/100000000000000 : ℝ)^53
        have hw : |(-258408889/5000000000 : ℝ)|=(258408889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-768518847/1000000000 : ℝ)|^69 ≤ (35489929564661/50000000000000 : ℝ)^53
        have hw : |(-768518847/1000000000 : ℝ)|=(768518847/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3648139889/10000000000 : ℝ)|^69 ≤ (13453542412069/50000000000000 : ℝ)^53
        have hw : |(3648139889/10000000000 : ℝ)|=(3648139889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308076_s1_s1_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (191555809/250000000 : ℝ)*x 0 + (630917679/2500000000 : ℝ)*x 1 + (1021094413/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (191555809/250000000 : ℝ)^69 ≤ (565631650497/800000000000 : ℝ)^53 := by
    have hnat : (191555809 : ℕ)^69*800000000000^53 ≤ 565631650497^53*250000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      191555809 250000000 565631650497 800000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (630917679/2500000000 : ℝ)^69 ≤ (16653834887829/100000000000000 : ℝ)^53 := by
    have hnat : (630917679 : ℕ)^69*100000000000000^53 ≤ 16653834887829^53*2500000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      630917679 2500000000 16653834887829 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1021094413/5000000000 : ℝ)^69 ≤ (12642208785483/100000000000000 : ℝ)^53 := by
    have hnat : (1021094413 : ℕ)^69*100000000000000^53 ≤ 12642208785483^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021094413 5000000000 12642208785483 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(191555809/250000000 : ℝ), (630917679/2500000000 : ℝ), (1021094413/5000000000 : ℝ)] ![(565631650497/800000000000 : ℝ), (16653834887829/100000000000000 : ℝ), (12642208785483/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(191555809/250000000 : ℝ)|^69 ≤ (565631650497/800000000000 : ℝ)^53
        have hw : |(191555809/250000000 : ℝ)|=(191555809/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(630917679/2500000000 : ℝ)|^69 ≤ (16653834887829/100000000000000 : ℝ)^53
        have hw : |(630917679/2500000000 : ℝ)|=(630917679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1021094413/5000000000 : ℝ)|^69 ≤ (12642208785483/100000000000000 : ℝ)^53
        have hw : |(1021094413/5000000000 : ℝ)|=(1021094413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308076_s1_s1_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3502160793/10000000000 : ℝ)*x 0 + (-41109563/62500000 : ℝ)*x 1 + (-2508630959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3502160793/10000000000 : ℝ)^69 ≤ (25513918448859/100000000000000 : ℝ)^53 := by
    have hnat : (3502160793 : ℕ)^69*100000000000000^53 ≤ 25513918448859^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3502160793 10000000000 25513918448859 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41109563/62500000 : ℝ)^69 ≤ (28980670049879/50000000000000 : ℝ)^53 := by
    have hnat : (41109563 : ℕ)^69*50000000000000^53 ≤ 28980670049879^53*62500000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41109563 62500000 28980670049879 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2508630959/10000000000 : ℝ)^69 ≤ (16524741433949/100000000000000 : ℝ)^53 := by
    have hnat : (2508630959 : ℕ)^69*100000000000000^53 ≤ 16524741433949^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2508630959 10000000000 16524741433949 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3502160793/10000000000 : ℝ), (-41109563/62500000 : ℝ), (-2508630959/10000000000 : ℝ)] ![(25513918448859/100000000000000 : ℝ), (28980670049879/50000000000000 : ℝ), (16524741433949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3502160793/10000000000 : ℝ)|^69 ≤ (25513918448859/100000000000000 : ℝ)^53
        have hw : |(3502160793/10000000000 : ℝ)|=(3502160793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-41109563/62500000 : ℝ)|^69 ≤ (28980670049879/50000000000000 : ℝ)^53
        have hw : |(-41109563/62500000 : ℝ)|=(41109563/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2508630959/10000000000 : ℝ)|^69 ≤ (16524741433949/100000000000000 : ℝ)^53
        have hw : |(-2508630959/10000000000 : ℝ)|=(2508630959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308076_s1_s1_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3210659767/5000000000 : ℝ)*x 0 + (196649/625000000 : ℝ)*x 1 + (5306088381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3210659767/5000000000 : ℝ)^69 ≤ (56175712955009/100000000000000 : ℝ)^53 := by
    have hnat : (3210659767 : ℕ)^69*100000000000000^53 ≤ 56175712955009^53*5000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3210659767 5000000000 56175712955009 100000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (196649/625000000 : ℝ)^69 ≤ (1378851019/50000000000000 : ℝ)^53 := by
    have hnat : (196649 : ℕ)^69*50000000000000^53 ≤ 1378851019^53*625000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196649 625000000 1378851019 50000000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5306088381/10000000000 : ℝ)^69 ≤ (5477691166449/12500000000000 : ℝ)^53 := by
    have hnat : (5306088381 : ℕ)^69*12500000000000^53 ≤ 5477691166449^53*10000000000^69 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5306088381 10000000000 5477691166449 12500000000000 69 53 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (69/16 : ℝ)) 69 53 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3210659767/5000000000 : ℝ), (196649/625000000 : ℝ), (5306088381/10000000000 : ℝ)] ![(56175712955009/100000000000000 : ℝ), (1378851019/50000000000000 : ℝ), (5477691166449/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3210659767/5000000000 : ℝ)|^69 ≤ (56175712955009/100000000000000 : ℝ)^53
        have hw : |(3210659767/5000000000 : ℝ)|=(3210659767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(196649/625000000 : ℝ)|^69 ≤ (1378851019/50000000000000 : ℝ)^53
        have hw : |(196649/625000000 : ℝ)|=(196649/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5306088381/10000000000 : ℝ)|^69 ≤ (5477691166449/12500000000000 : ℝ)^53
        have hw : |(5306088381/10000000000 : ℝ)|=(5306088381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308076_s1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((86999/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(86999/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-3551/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-3551/4000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(93357/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(93357/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((70077/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(70077/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-72891/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-72891/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19567/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19567/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (3861/5000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (3861/5000 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (3861/5000 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (11517/6250 : ℝ) := by
    linarith only [f.Tcap]
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base33 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0,f.sum]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base54 : ((-1 : ℝ)*N 2+(1 : ℝ)*P 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 2]
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
  have s1_pow0 : (86999/100000 : ℝ) ^ (17/4 : ℝ) ≤ (55326807111542631393/100000000000000000000 : ℝ) := by
    have hpowers : (86999/100000 : ℝ)^17 ≤ (55326807111542631393/100000000000000000000 : ℝ)^4 := by
      have hnat : (86999 : ℕ)^17*100000000000000000000^4 ≤ 55326807111542631393^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        86999 100000 55326807111542631393 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (86999/100000 : ℝ)) (X := (55326807111542631393/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (155326807111542631393/100000000000000000000 : ℝ) ≤ (2218345321840679/2000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (155326807111542631393/100000000000000000000 : ℝ)^4 ≤ (2218345321840679/2000000000000000 : ℝ)^17 := by
      have hnat : (155326807111542631393 : ℕ)^4*2000000000000000^17 ≤ 2218345321840679^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        155326807111542631393 100000000000000000000 2218345321840679 2000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2218345321840679/2000000000000000 : ℝ)) (X := (155326807111542631393/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (105326807111542631393/50000000000000000000 : ℝ) ≤ (11916092403687311/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (105326807111542631393/50000000000000000000 : ℝ)^4 ≤ (11916092403687311/10000000000000000 : ℝ)^17 := by
      have hnat : (105326807111542631393 : ℕ)^4*10000000000000000^17 ≤ 11916092403687311^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        105326807111542631393 50000000000000000000 11916092403687311 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11916092403687311/10000000000000000 : ℝ)) (X := (105326807111542631393/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(19849574712789/158180000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(206091448620979/2174975000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (86999/100000 : ℝ)) (alpha := (19849574712789/158180000000000 : ℝ)) (beta := (206091448620979/2174975000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (86999/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(19849574712789/158180000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(206091448620979/2174975000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (3551/4000 : ℝ) ^ (17/4 : ℝ) ≤ (60288627095446667683/100000000000000000000 : ℝ) := by
    have hpowers : (3551/4000 : ℝ)^17 ≤ (60288627095446667683/100000000000000000000 : ℝ)^4 := by
      have hnat : (3551 : ℕ)^17*100000000000000000000^4 ≤ 60288627095446667683^4*4000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3551 4000 60288627095446667683 100000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3551/4000 : ℝ)) (X := (60288627095446667683/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (160288627095446667683/100000000000000000000 : ℝ) ≤ (1396762012693709/1250000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (160288627095446667683/100000000000000000000 : ℝ)^4 ≤ (1396762012693709/1250000000000000 : ℝ)^17 := by
      have hnat : (160288627095446667683 : ℕ)^4*1250000000000000^17 ≤ 1396762012693709^17*100000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        160288627095446667683 100000000000000000000 1396762012693709 1250000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1396762012693709/1250000000000000 : ℝ)) (X := (160288627095446667683/100000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (110288627095446667683/50000000000000000000 : ℝ) ≤ (75286626134431/62500000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (110288627095446667683/50000000000000000000 : ℝ)^4 ≤ (75286626134431/62500000000000 : ℝ)^17 := by
      have hnat : (110288627095446667683 : ℕ)^4*62500000000000^17 ≤ 75286626134431^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        110288627095446667683 50000000000000000000 75286626134431 62500000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (75286626134431/62500000000000 : ℝ)) (X := (110288627095446667683/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(146762012693709/1109687500000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2))+(108970509994911/1109687500000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (3551/4000 : ℝ)) (alpha := (146762012693709/1109687500000000 : ℝ)) (beta := (108970509994911/1109687500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 2) ≤ (3551/4000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(146762012693709/1109687500000000 : ℝ)*((1 : ℝ)*pair X 1 2)+(108970509994911/1109687500000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (93357/100000 : ℝ) ^ (17/4 : ℝ) ≤ (14933247630311514199/20000000000000000000 : ℝ) := by
    have hpowers : (93357/100000 : ℝ)^17 ≤ (14933247630311514199/20000000000000000000 : ℝ)^4 := by
      have hnat : (93357 : ℕ)^17*20000000000000000000^4 ≤ 14933247630311514199^4*100000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        93357 100000 14933247630311514199 20000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (93357/100000 : ℝ)) (X := (14933247630311514199/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (34933247630311514199/20000000000000000000 : ℝ) ≤ (712640274226859/625000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (34933247630311514199/20000000000000000000 : ℝ)^4 ≤ (712640274226859/625000000000000 : ℝ)^17 := by
      have hnat : (34933247630311514199 : ℕ)^4*625000000000000^17 ≤ 712640274226859^17*20000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34933247630311514199 20000000000000000000 712640274226859 625000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (712640274226859/625000000000000 : ℝ)) (X := (34933247630311514199/20000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (24933247630311514199/10000000000000000000 : ℝ) ≤ (6199115582251151/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (24933247630311514199/10000000000000000000 : ℝ)^4 ≤ (6199115582251151/5000000000000000 : ℝ)^17 := by
      have hnat : (24933247630311514199 : ℕ)^4*5000000000000000^17 ≤ 6199115582251151^17*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24933247630311514199 10000000000000000000 6199115582251151 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6199115582251151/5000000000000000 : ℝ)) (X := (24933247630311514199/10000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(87640274226859/583481250000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(497993388436279/4667850000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (93357/100000 : ℝ)) (alpha := (87640274226859/583481250000000 : ℝ)) (beta := (497993388436279/4667850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (93357/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(87640274226859/583481250000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(497993388436279/4667850000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1391738329/10000000000 : ℝ)*X 0 0+(-6372047997/10000000000 : ℝ)*X 0 1+(1157852759/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308076_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((6522540973/10000000000 : ℝ)*X 1 0+(1636733859/5000000000 : ℝ)*X 1 1+(2826583269/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308076_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-563753649/5000000000 : ℝ)*X 0 0+(-1903895433/2500000000 : ℝ)*X 0 1+(3343761893/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308076_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((2612901107/5000000000 : ℝ)*X 1 0+(4664521947/10000000000 : ℝ)*X 1 1+(2835222/9765625 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308076_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((27819373/50000000 : ℝ)*X 2 0+(-5430378499/10000000000 : ℝ)*X 2 1+(-733890859/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308076_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((3150632541/10000000000 : ℝ)*X 0 0+(38245183/5000000000 : ℝ)*X 0 1+(1645886149/2000000000 : ℝ)*X 0 2+(3150632541/10000000000 : ℝ)*X 1 0+(38245183/5000000000 : ℝ)*X 1 1+(1645886149/2000000000 : ℝ)*X 1 2+(3150632541/10000000000 : ℝ)*X 2 0+(38245183/5000000000 : ℝ)*X 2 1+(1645886149/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308076_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-1142374289/10000000000 : ℝ)*X 0 0+(-4387226713/10000000000 : ℝ)*X 0 1+(3370952313/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308076_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((1546551507/2000000000 : ℝ)*X 1 0+(1242849327/5000000000 : ℝ)*X 1 1+(197698733/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308076_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((4906575679/10000000000 : ℝ)*X 2 0+(-5754677697/10000000000 : ℝ)*X 2 1+(-1926661469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308076_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1928281861/10000000000 : ℝ)*X 0 0+(-76013/2500000000 : ℝ)*X 0 1+(9085943937/10000000000 : ℝ)*X 0 2+(1928281861/10000000000 : ℝ)*X 1 0+(-76013/2500000000 : ℝ)*X 1 1+(9085943937/10000000000 : ℝ)*X 1 2+(1928281861/10000000000 : ℝ)*X 2 0+(-76013/2500000000 : ℝ)*X 2 1+(9085943937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308076_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-258408889/5000000000 : ℝ)*X 0 0+(-768518847/1000000000 : ℝ)*X 0 1+(3648139889/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308076_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((191555809/250000000 : ℝ)*X 1 0+(630917679/2500000000 : ℝ)*X 1 1+(1021094413/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308076_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((3502160793/10000000000 : ℝ)*X 2 0+(-41109563/62500000 : ℝ)*X 2 1+(-2508630959/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308076_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((3210659767/5000000000 : ℝ)*X 0 0+(196649/625000000 : ℝ)*X 0 1+(5306088381/10000000000 : ℝ)*X 0 2+(3210659767/5000000000 : ℝ)*X 1 0+(196649/625000000 : ℝ)*X 1 1+(5306088381/10000000000 : ℝ)*X 1 2+(3210659767/5000000000 : ℝ)*X 2 0+(196649/625000000 : ℝ)*X 2 1+(5306088381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308076_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((70077/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(70077/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1167176728097170544076482864851/91038825752187500000000000000000000 : ℝ) := by norm_num
    linear_combination (139612946441/1000000000000 : ℝ)*(base3) + (263885832863/500000000000 : ℝ)*(base7) + (324547/125000000000 : ℝ)*(base40) + (22421412433/25000000000 : ℝ)*(base54) + (609313491491/250000000000 : ℝ)*(major_s1_0) + (609313491491/250000000000 : ℝ)*(major_s1_1) + (1540397468643/1000000000000 : ℝ)*(major_s1_2) + (3685029/1000000000000 : ℝ)*(sp_s1_0) + (374383448541/125000000000 : ℝ)*(sp_s1_7) + (1567342109899/500000000000 : ℝ)*(sp_s1_8) + (2098148387371/1000000000000 : ℝ)*(sp_s1_9) + (261638994401/250000000000 : ℝ)*(sp_s1_13) + (66388667/1000000000000 : ℝ)*(sp_s1_16) + (8071/50000000000 : ℝ)*(sp_s1_20) + (77762695853/50000000000 : ℝ)*(f.failure) + (2995071273357/1000000000000 : ℝ)*(f.sum) + (480549509656200211/12557223750000000000000000000000 : ℝ)*base63 + (44299302314233/70725000000000000000000000 : ℝ)*base64 + (368139853174601/1109687500000000000000000000 : ℝ)*base67 + (18362392078373/35362500000000000000000000 : ℝ)*base69 + (46324692360620459/1118728050000000000000000000000 : ℝ)*base70 + (127159541550479/543743750000000000000000000 : ℝ)*base73 + (416320441884809/4438750000000000000000000000 : ℝ)*base75 + (3346652634817/39545000000000000000000000 : ℝ)*base77 + (343658642676703565021/386166811250000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (517/5000000000000000 : ℝ)*base86 + (517/5000000000000000 : ℝ)*base88 + (4483/5000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-72891/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-72891/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (635884531432748622202934323209/182077651504375000000000000000000000 : ℝ) := by norm_num
    linear_combination (90971/125000000000 : ℝ)*(base3) + (76581668263/125000000000 : ℝ)*(base7) + (136059736571/250000000000 : ℝ)*(base33) + (21066429363/500000000000 : ℝ)*(base40) + (1361839996749/1000000000000 : ℝ)*(major_s1_0) + (953039471517/500000000000 : ℝ)*(major_s1_1) + (953039471517/500000000000 : ℝ)*(major_s1_2) + (19764083/1000000000000 : ℝ)*(sp_s1_13) + (277442323043/125000000000 : ℝ)*(sp_s1_14) + (83708560233/50000000000 : ℝ)*(sp_s1_15) + (1675225372623/1000000000000 : ℝ)*(sp_s1_16) + (1828934800533/1000000000000 : ℝ)*(sp_s1_20) + (70572573/62500000000 : ℝ)*(sp_s1_22) + (74265437/1000000000000 : ℝ)*(sp_s1_23) + (1216301946279/1000000000000 : ℝ)*(f.failure) + (277442323043/125000000000 : ℝ)*(f.sum) + (326250129931461213/2877697109375000000000000000000 : ℝ)*base62 + (11724268781537/64831250000000000000000000 : ℝ)*base64 + (84935508311553/554843750000000000000000000 : ℝ)*base67 + (120197513309867/129662500000000000000000000 : ℝ)*base68 + (16927468212035467/745818700000000000000000000000 : ℝ)*base71 + (938194260230669/2174975000000000000000000000 : ℝ)*base72 + (1241703887304573/2219375000000000000000000000 : ℝ)*base74 + (37582433332683/158180000000000000000000000 : ℝ)*base77 + (14637008489102584703/48270851406250000000000000000000 : ℝ)*base78 + (28369/100000000000000000 : ℝ)*base87 + (71631/100000000000000000 : ℝ)*base88 + (71631/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19567/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19567/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (5598858579478312758484620008983/1092465909026250000000000000000000000 : ℝ) := by norm_num
    linear_combination (251155239581/500000000000 : ℝ)*(base3) + (423876574791/500000000000 : ℝ)*(base7) + (1988317/1000000000000 : ℝ)*(base22) + (28753763767/100000000000 : ℝ)*(base40) + (653577368281/250000000000 : ℝ)*(major_s1_0) + (653577368281/250000000000 : ℝ)*(major_s1_1) + (653577368281/250000000000 : ℝ)*(major_s1_2) + (4322019/1000000000000 : ℝ)*(sp_s1_0) + (4093659/1000000000000 : ℝ)*(sp_s1_1) + (453137/25000000000 : ℝ)*(sp_s1_16) + (303965292229/100000000000 : ℝ)*(sp_s1_21) + (885490907453/250000000000 : ℝ)*(sp_s1_22) + (189977320657/62500000000 : ℝ)*(sp_s1_23) + (2013678769433/1000000000000 : ℝ)*(sp_s1_27) + (1668236099013/1000000000000 : ℝ)*(f.failure) + (3039657244309/1000000000000 : ℝ)*(f.sum) + (44063038460380629017/414388383750000000000000000000000 : ℝ)*base62 + (502292491198831/4667850000000000000000000000 : ℝ)*base65 + (1130606044156961/4438750000000000000000000000 : ℝ)*base66 + (1172974045471837/4667850000000000000000000000 : ℝ)*base68 + (90712468609925141/839046037500000000000000000000 : ℝ)*base71 + (493550545518357/1087487500000000000000000000 : ℝ)*base72 + (220520208297553/2219375000000000000000000000 : ℝ)*base74 + (539478902257/1581800000000000000000000 : ℝ)*base77 + (133249426805914330489/386166811250000000000000000000000 : ℝ)*base78 + (26243/100000000000000000 : ℝ)*base87 + (26243/100000000000000000 : ℝ)*base89 + (26243/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (69/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, false, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((86999/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(86999/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-3551/4000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-3551/4000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(93357/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(93357/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((70077/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(70077/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-72891/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 0 2+(-72891/100000 : ℝ)*X 2 1+(-1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19567/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19567/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308076_s1 p hpa hpb X hX hprev0

#print axioms solution
