-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c307060_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:14:57.290068+00:00
-- url     : https://prove2.me/submissions/69f77898-bea6-491e-bb4d-b639f5f39859

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
theorem collision_support_c307060_s1_s1_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-809934267/5000000000 : ℝ)*x 0 + (2231252157/5000000000 : ℝ)*x 1 + (-256509839/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (809934267/5000000000 : ℝ)^17 ≤ (1850430469199/20000000000000 : ℝ)^13 := by
    have hnat : (809934267 : ℕ)^17*20000000000000^13 ≤ 1850430469199^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      809934267 5000000000 1850430469199 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2231252157/5000000000 : ℝ)^17 ≤ (6962844407019/20000000000000 : ℝ)^13 := by
    have hnat : (2231252157 : ℕ)^17*20000000000000^13 ≤ 6962844407019^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2231252157 5000000000 6962844407019 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256509839/400000000 : ℝ)^17 ≤ (55933625609893/100000000000000 : ℝ)^13 := by
    have hnat : (256509839 : ℕ)^17*100000000000000^13 ≤ 55933625609893^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256509839 400000000 55933625609893 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-809934267/5000000000 : ℝ), (2231252157/5000000000 : ℝ), (-256509839/400000000 : ℝ)] ![(1850430469199/20000000000000 : ℝ), (6962844407019/20000000000000 : ℝ), (55933625609893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-809934267/5000000000 : ℝ)|^17 ≤ (1850430469199/20000000000000 : ℝ)^13
        have hw : |(-809934267/5000000000 : ℝ)|=(809934267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2231252157/5000000000 : ℝ)|^17 ≤ (6962844407019/20000000000000 : ℝ)^13
        have hw : |(2231252157/5000000000 : ℝ)|=(2231252157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-256509839/400000000 : ℝ)|^17 ≤ (55933625609893/100000000000000 : ℝ)^13
        have hw : |(-256509839/400000000 : ℝ)|=(256509839/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307060_s1_s1_1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (446169057/1000000000 : ℝ)*x 0 + (-1620209127/10000000000 : ℝ)*x 1 + (-6413250749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (446169057/1000000000 : ℝ)^17 ≤ (17402960242147/50000000000000 : ℝ)^13 := by
    have hnat : (446169057 : ℕ)^17*50000000000000^13 ≤ 17402960242147^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446169057 1000000000 17402960242147 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1620209127/10000000000 : ℝ)^17 ≤ (462734817661/5000000000000 : ℝ)^13 := by
    have hnat : (1620209127 : ℕ)^17*5000000000000^13 ≤ 462734817661^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1620209127 10000000000 462734817661 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6413250749/10000000000 : ℝ)^17 ≤ (1398484578673/2500000000000 : ℝ)^13 := by
    have hnat : (6413250749 : ℕ)^17*2500000000000^13 ≤ 1398484578673^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6413250749 10000000000 1398484578673 2500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(446169057/1000000000 : ℝ), (-1620209127/10000000000 : ℝ), (-6413250749/10000000000 : ℝ)] ![(17402960242147/50000000000000 : ℝ), (462734817661/5000000000000 : ℝ), (1398484578673/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(446169057/1000000000 : ℝ)|^17 ≤ (17402960242147/50000000000000 : ℝ)^13
        have hw : |(446169057/1000000000 : ℝ)|=(446169057/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1620209127/10000000000 : ℝ)|^17 ≤ (462734817661/5000000000000 : ℝ)^13
        have hw : |(-1620209127/10000000000 : ℝ)|=(1620209127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6413250749/10000000000 : ℝ)|^17 ≤ (1398484578673/2500000000000 : ℝ)^13
        have hw : |(-6413250749/10000000000 : ℝ)|=(6413250749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307060_s1_s1_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1067903151/10000000000 : ℝ)*x 0 + (109871701/500000000 : ℝ)*x 1 + (-4249786123/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1067903151/10000000000 : ℝ)^17 ≤ (335350234147/6250000000000 : ℝ)^13 := by
    have hnat : (1067903151 : ℕ)^17*6250000000000^13 ≤ 335350234147^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067903151 10000000000 335350234147 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109871701/500000000 : ℝ)^17 ≤ (430802716213/3125000000000 : ℝ)^13 := by
    have hnat : (109871701 : ℕ)^17*3125000000000^13 ≤ 430802716213^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109871701 500000000 430802716213 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4249786123/5000000000 : ℝ)^17 ≤ (80848709324357/100000000000000 : ℝ)^13 := by
    have hnat : (4249786123 : ℕ)^17*100000000000000^13 ≤ 80848709324357^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249786123 5000000000 80848709324357 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1067903151/10000000000 : ℝ), (109871701/500000000 : ℝ), (-4249786123/5000000000 : ℝ)] ![(335350234147/6250000000000 : ℝ), (430802716213/3125000000000 : ℝ), (80848709324357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1067903151/10000000000 : ℝ)|^17 ≤ (335350234147/6250000000000 : ℝ)^13
        have hw : |(-1067903151/10000000000 : ℝ)|=(1067903151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(109871701/500000000 : ℝ)|^17 ≤ (430802716213/3125000000000 : ℝ)^13
        have hw : |(109871701/500000000 : ℝ)|=(109871701/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4249786123/5000000000 : ℝ)|^17 ≤ (80848709324357/100000000000000 : ℝ)^13
        have hw : |(-4249786123/5000000000 : ℝ)|=(4249786123/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307060_s1_s1_8 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (249867569/1000000000 : ℝ)*x 0 + (-26227847/400000000 : ℝ)*x 1 + (-4250120499/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (249867569/1000000000 : ℝ)^17 ≤ (16307592782231/100000000000000 : ℝ)^13 := by
    have hnat : (249867569 : ℕ)^17*100000000000000^13 ≤ 16307592782231^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249867569 1000000000 16307592782231 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26227847/400000000 : ℝ)^17 ≤ (2835379257947/100000000000000 : ℝ)^13 := by
    have hnat : (26227847 : ℕ)^17*100000000000000^13 ≤ 2835379257947^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26227847 400000000 2835379257947 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4250120499/5000000000 : ℝ)^17 ≤ (80857027956911/100000000000000 : ℝ)^13 := by
    have hnat : (4250120499 : ℕ)^17*100000000000000^13 ≤ 80857027956911^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4250120499 5000000000 80857027956911 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(249867569/1000000000 : ℝ), (-26227847/400000000 : ℝ), (-4250120499/5000000000 : ℝ)] ![(16307592782231/100000000000000 : ℝ), (2835379257947/100000000000000 : ℝ), (80857027956911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(249867569/1000000000 : ℝ)|^17 ≤ (16307592782231/100000000000000 : ℝ)^13
        have hw : |(249867569/1000000000 : ℝ)|=(249867569/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-26227847/400000000 : ℝ)|^17 ≤ (2835379257947/100000000000000 : ℝ)^13
        have hw : |(-26227847/400000000 : ℝ)|=(26227847/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4250120499/5000000000 : ℝ)|^17 ≤ (80857027956911/100000000000000 : ℝ)^13
        have hw : |(-4250120499/5000000000 : ℝ)|=(4250120499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307060_s1_s1_9 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (445176203/2000000000 : ℝ)*x 0 + (8103532037/10000000000 : ℝ)*x 1 + (215251417/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (445176203/2000000000 : ℝ)^17 ≤ (1752440680201/12500000000000 : ℝ)^13 := by
    have hnat : (445176203 : ℕ)^17*12500000000000^13 ≤ 1752440680201^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445176203 2000000000 1752440680201 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8103532037/10000000000 : ℝ)^17 ≤ (37979055389607/50000000000000 : ℝ)^13 := by
    have hnat : (8103532037 : ℕ)^17*50000000000000^13 ≤ 37979055389607^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8103532037 10000000000 37979055389607 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215251417/1250000000 : ℝ)^17 ≤ (10022363770831/100000000000000 : ℝ)^13 := by
    have hnat : (215251417 : ℕ)^17*100000000000000^13 ≤ 10022363770831^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215251417 1250000000 10022363770831 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(445176203/2000000000 : ℝ), (8103532037/10000000000 : ℝ), (215251417/1250000000 : ℝ)] ![(1752440680201/12500000000000 : ℝ), (37979055389607/50000000000000 : ℝ), (10022363770831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(445176203/2000000000 : ℝ)|^17 ≤ (1752440680201/12500000000000 : ℝ)^13
        have hw : |(445176203/2000000000 : ℝ)|=(445176203/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(8103532037/10000000000 : ℝ)|^17 ≤ (37979055389607/50000000000000 : ℝ)^13
        have hw : |(8103532037/10000000000 : ℝ)|=(8103532037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215251417/1250000000 : ℝ)|^17 ≤ (10022363770831/100000000000000 : ℝ)^13
        have hw : |(215251417/1250000000 : ℝ)|=(215251417/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307060_s1_s1_13 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2185566899/5000000000 : ℝ)*x 0 + (7287562351/10000000000 : ℝ)*x 1 + (-1727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2185566899/5000000000 : ℝ)^17 ≤ (16942507003627/50000000000000 : ℝ)^13 := by
    have hnat : (2185566899 : ℕ)^17*50000000000000^13 ≤ 16942507003627^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185566899 5000000000 16942507003627 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7287562351/10000000000 : ℝ)^17 ≤ (66114985834759/100000000000000 : ℝ)^13 := by
    have hnat : (7287562351 : ℕ)^17*100000000000000^13 ≤ 66114985834759^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7287562351 10000000000 66114985834759 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1727/10000000000 : ℝ)^17 ≤ (143371/100000000000000 : ℝ)^13 := by
    have hnat : (1727 : ℕ)^17*100000000000000^13 ≤ 143371^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1727 10000000000 143371 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2185566899/5000000000 : ℝ), (7287562351/10000000000 : ℝ), (-1727/10000000000 : ℝ)] ![(16942507003627/50000000000000 : ℝ), (66114985834759/100000000000000 : ℝ), (143371/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2185566899/5000000000 : ℝ)|^17 ≤ (16942507003627/50000000000000 : ℝ)^13
        have hw : |(2185566899/5000000000 : ℝ)|=(2185566899/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7287562351/10000000000 : ℝ)|^17 ≤ (66114985834759/100000000000000 : ℝ)^13
        have hw : |(7287562351/10000000000 : ℝ)|=(7287562351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1727/10000000000 : ℝ)|^17 ≤ (143371/100000000000000 : ℝ)^13
        have hw : |(-1727/10000000000 : ℝ)|=(1727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307060_s1_s1_14 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1237593953/10000000000 : ℝ)*x 0 + (106869039/625000000 : ℝ)*x 1 + (-4358458893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1237593953/10000000000 : ℝ)^17 ≤ (6506860026723/100000000000000 : ℝ)^13 := by
    have hnat : (1237593953 : ℕ)^17*100000000000000^13 ≤ 6506860026723^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1237593953 10000000000 6506860026723 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (106869039/625000000 : ℝ)^17 ≤ (4965159918371/50000000000000 : ℝ)^13 := by
    have hnat : (106869039 : ℕ)^17*50000000000000^13 ≤ 4965159918371^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106869039 625000000 4965159918371 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4358458893/5000000000 : ℝ)^17 ≤ (20890705031711/25000000000000 : ℝ)^13 := by
    have hnat : (4358458893 : ℕ)^17*25000000000000^13 ≤ 20890705031711^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358458893 5000000000 20890705031711 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1237593953/10000000000 : ℝ), (106869039/625000000 : ℝ), (-4358458893/5000000000 : ℝ)] ![(6506860026723/100000000000000 : ℝ), (4965159918371/50000000000000 : ℝ), (20890705031711/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1237593953/10000000000 : ℝ)|^17 ≤ (6506860026723/100000000000000 : ℝ)^13
        have hw : |(-1237593953/10000000000 : ℝ)|=(1237593953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(106869039/625000000 : ℝ)|^17 ≤ (4965159918371/50000000000000 : ℝ)^13
        have hw : |(106869039/625000000 : ℝ)|=(106869039/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4358458893/5000000000 : ℝ)|^17 ≤ (20890705031711/25000000000000 : ℝ)^13
        have hw : |(-4358458893/5000000000 : ℝ)|=(4358458893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307060_s1_s1_15 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (133581663/1000000000 : ℝ)*x 0 + (-404503457/2500000000 : ℝ)*x 1 + (-8717603557/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133581663/1000000000 : ℝ)^17 ≤ (898785150131/12500000000000 : ℝ)^13 := by
    have hnat : (133581663 : ℕ)^17*12500000000000^13 ≤ 898785150131^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133581663 1000000000 898785150131 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (404503457/2500000000 : ℝ)^17 ≤ (1847660358531/20000000000000 : ℝ)^13 := by
    have hnat : (404503457 : ℕ)^17*20000000000000^13 ≤ 1847660358531^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      404503457 2500000000 1847660358531 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8717603557/10000000000 : ℝ)^17 ≤ (83571416991301/100000000000000 : ℝ)^13 := by
    have hnat : (8717603557 : ℕ)^17*100000000000000^13 ≤ 83571416991301^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8717603557 10000000000 83571416991301 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133581663/1000000000 : ℝ), (-404503457/2500000000 : ℝ), (-8717603557/10000000000 : ℝ)] ![(898785150131/12500000000000 : ℝ), (1847660358531/20000000000000 : ℝ), (83571416991301/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133581663/1000000000 : ℝ)|^17 ≤ (898785150131/12500000000000 : ℝ)^13
        have hw : |(133581663/1000000000 : ℝ)|=(133581663/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-404503457/2500000000 : ℝ)|^17 ≤ (1847660358531/20000000000000 : ℝ)^13
        have hw : |(-404503457/2500000000 : ℝ)|=(404503457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8717603557/10000000000 : ℝ)|^17 ≤ (83571416991301/100000000000000 : ℝ)^13
        have hw : |(-8717603557/10000000000 : ℝ)|=(8717603557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307060_s1_s1_16 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (420048597/625000000 : ℝ)*x 0 + (923058583/2500000000 : ℝ)*x 1 + (1072287689/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (420048597/625000000 : ℝ)^17 ≤ (59472724627123/100000000000000 : ℝ)^13 := by
    have hnat : (420048597 : ℕ)^17*100000000000000^13 ≤ 59472724627123^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420048597 625000000 59472724627123 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (923058583/2500000000 : ℝ)^17 ≤ (27173619440553/100000000000000 : ℝ)^13 := by
    have hnat : (923058583 : ℕ)^17*100000000000000^13 ≤ 27173619440553^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      923058583 2500000000 27173619440553 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1072287689/5000000000 : ℝ)^17 ≤ (13353655924281/100000000000000 : ℝ)^13 := by
    have hnat : (1072287689 : ℕ)^17*100000000000000^13 ≤ 13353655924281^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072287689 5000000000 13353655924281 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(420048597/625000000 : ℝ), (923058583/2500000000 : ℝ), (1072287689/5000000000 : ℝ)] ![(59472724627123/100000000000000 : ℝ), (27173619440553/100000000000000 : ℝ), (13353655924281/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(420048597/625000000 : ℝ)|^17 ≤ (59472724627123/100000000000000 : ℝ)^13
        have hw : |(420048597/625000000 : ℝ)|=(420048597/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(923058583/2500000000 : ℝ)|^17 ≤ (27173619440553/100000000000000 : ℝ)^13
        have hw : |(923058583/2500000000 : ℝ)|=(923058583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1072287689/5000000000 : ℝ)|^17 ≤ (13353655924281/100000000000000 : ℝ)^13
        have hw : |(1072287689/5000000000 : ℝ)|=(1072287689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307060_s1_s1_20 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4427222557/5000000000 : ℝ)*x 0 + (144319667/625000000 : ℝ)*x 1 + (1313/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4427222557/5000000000 : ℝ)^17 ≤ (42645509602259/50000000000000 : ℝ)^13 := by
    have hnat : (4427222557 : ℕ)^17*50000000000000^13 ≤ 42645509602259^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4427222557 5000000000 42645509602259 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (144319667/625000000 : ℝ)^17 ≤ (14708980693781/100000000000000 : ℝ)^13 := by
    have hnat : (144319667 : ℕ)^17*100000000000000^13 ≤ 14708980693781^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      144319667 625000000 14708980693781 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1313/10000000000 : ℝ)^17 ≤ (100187/100000000000000 : ℝ)^13 := by
    have hnat : (1313 : ℕ)^17*100000000000000^13 ≤ 100187^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313 10000000000 100187 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4427222557/5000000000 : ℝ), (144319667/625000000 : ℝ), (1313/10000000000 : ℝ)] ![(42645509602259/50000000000000 : ℝ), (14708980693781/100000000000000 : ℝ), (100187/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4427222557/5000000000 : ℝ)|^17 ≤ (42645509602259/50000000000000 : ℝ)^13
        have hw : |(4427222557/5000000000 : ℝ)|=(4427222557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(144319667/625000000 : ℝ)|^17 ≤ (14708980693781/100000000000000 : ℝ)^13
        have hw : |(144319667/625000000 : ℝ)|=(144319667/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1313/10000000000 : ℝ)|^17 ≤ (100187/100000000000000 : ℝ)^13
        have hw : |(1313/10000000000 : ℝ)|=(1313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307060_s1_s1_21 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-325598507/2000000000 : ℝ)*x 0 + (3519787827/10000000000 : ℝ)*x 1 + (-900877761/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (325598507/2000000000 : ℝ)^17 ≤ (9312878128119/100000000000000 : ℝ)^13 := by
    have hnat : (325598507 : ℕ)^17*100000000000000^13 ≤ 9312878128119^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325598507 2000000000 9312878128119 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3519787827/10000000000 : ℝ)^17 ≤ (12763009722463/50000000000000 : ℝ)^13 := by
    have hnat : (3519787827 : ℕ)^17*50000000000000^13 ≤ 12763009722463^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3519787827 10000000000 12763009722463 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (900877761/1250000000 : ℝ)^17 ≤ (3258055121043/5000000000000 : ℝ)^13 := by
    have hnat : (900877761 : ℕ)^17*5000000000000^13 ≤ 3258055121043^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900877761 1250000000 3258055121043 5000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-325598507/2000000000 : ℝ), (3519787827/10000000000 : ℝ), (-900877761/1250000000 : ℝ)] ![(9312878128119/100000000000000 : ℝ), (12763009722463/50000000000000 : ℝ), (3258055121043/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-325598507/2000000000 : ℝ)|^17 ≤ (9312878128119/100000000000000 : ℝ)^13
        have hw : |(-325598507/2000000000 : ℝ)|=(325598507/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3519787827/10000000000 : ℝ)|^17 ≤ (12763009722463/50000000000000 : ℝ)^13
        have hw : |(3519787827/10000000000 : ℝ)|=(3519787827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-900877761/1250000000 : ℝ)|^17 ≤ (3258055121043/5000000000000 : ℝ)^13
        have hw : |(-900877761/1250000000 : ℝ)|=(900877761/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307060_s1_s1_22 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1849190877/2500000000 : ℝ)*x 0 + (-630544421/5000000000 : ℝ)*x 1 + (-890251883/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1849190877/2500000000 : ℝ)^17 ≤ (33706750518599/50000000000000 : ℝ)^13 := by
    have hnat : (1849190877 : ℕ)^17*50000000000000^13 ≤ 33706750518599^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1849190877 2500000000 33706750518599 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (630544421/5000000000 : ℝ)^17 ≤ (6668866861081/100000000000000 : ℝ)^13 := by
    have hnat : (630544421 : ℕ)^17*100000000000000^13 ≤ 6668866861081^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      630544421 5000000000 6668866861081 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (890251883/2500000000 : ℝ)^17 ≤ (25917632092769/100000000000000 : ℝ)^13 := by
    have hnat : (890251883 : ℕ)^17*100000000000000^13 ≤ 25917632092769^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890251883 2500000000 25917632092769 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1849190877/2500000000 : ℝ), (-630544421/5000000000 : ℝ), (-890251883/2500000000 : ℝ)] ![(33706750518599/50000000000000 : ℝ), (6668866861081/100000000000000 : ℝ), (25917632092769/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1849190877/2500000000 : ℝ)|^17 ≤ (33706750518599/50000000000000 : ℝ)^13
        have hw : |(1849190877/2500000000 : ℝ)|=(1849190877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-630544421/5000000000 : ℝ)|^17 ≤ (6668866861081/100000000000000 : ℝ)^13
        have hw : |(-630544421/5000000000 : ℝ)|=(630544421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-890251883/2500000000 : ℝ)|^17 ≤ (25917632092769/100000000000000 : ℝ)^13
        have hw : |(-890251883/2500000000 : ℝ)|=(890251883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307060_s1_s1_23 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (395350237/2000000000 : ℝ)*x 0 + (7630129853/10000000000 : ℝ)*x 1 + (2670336479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (395350237/2000000000 : ℝ)^17 ≤ (12003885835919/100000000000000 : ℝ)^13 := by
    have hnat : (395350237 : ℕ)^17*100000000000000^13 ≤ 12003885835919^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      395350237 2000000000 12003885835919 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7630129853/10000000000 : ℝ)^17 ≤ (14041642214133/20000000000000 : ℝ)^13 := by
    have hnat : (7630129853 : ℕ)^17*20000000000000^13 ≤ 14041642214133^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7630129853 10000000000 14041642214133 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2670336479/10000000000 : ℝ)^17 ≤ (1778790307509/10000000000000 : ℝ)^13 := by
    have hnat : (2670336479 : ℕ)^17*10000000000000^13 ≤ 1778790307509^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2670336479 10000000000 1778790307509 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(395350237/2000000000 : ℝ), (7630129853/10000000000 : ℝ), (2670336479/10000000000 : ℝ)] ![(12003885835919/100000000000000 : ℝ), (14041642214133/20000000000000 : ℝ), (1778790307509/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(395350237/2000000000 : ℝ)|^17 ≤ (12003885835919/100000000000000 : ℝ)^13
        have hw : |(395350237/2000000000 : ℝ)|=(395350237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7630129853/10000000000 : ℝ)|^17 ≤ (14041642214133/20000000000000 : ℝ)^13
        have hw : |(7630129853/10000000000 : ℝ)|=(7630129853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2670336479/10000000000 : ℝ)|^17 ≤ (1778790307509/10000000000000 : ℝ)^13
        have hw : |(2670336479/10000000000 : ℝ)|=(2670336479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307060_s1_s1_27 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (28551287/31250000 : ℝ)*x 0 + (1867004913/10000000000 : ℝ)*x 1 + (-183/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (28551287/31250000 : ℝ)^17 ≤ (2776877134213/3125000000000 : ℝ)^13 := by
    have hnat : (28551287 : ℕ)^17*3125000000000^13 ≤ 2776877134213^13*31250000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28551287 31250000 2776877134213 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1867004913/10000000000 : ℝ)^17 ≤ (2227986327203/20000000000000 : ℝ)^13 := by
    have hnat : (1867004913 : ℕ)^17*20000000000000^13 ≤ 2227986327203^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867004913 10000000000 2227986327203 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (183/2000000000 : ℝ)^17 ≤ (2499/4000000000000 : ℝ)^13 := by
    have hnat : (183 : ℕ)^17*4000000000000^13 ≤ 2499^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183 2000000000 2499 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(28551287/31250000 : ℝ), (1867004913/10000000000 : ℝ), (-183/2000000000 : ℝ)] ![(2776877134213/3125000000000 : ℝ), (2227986327203/20000000000000 : ℝ), (2499/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(28551287/31250000 : ℝ)|^17 ≤ (2776877134213/3125000000000 : ℝ)^13
        have hw : |(28551287/31250000 : ℝ)|=(28551287/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1867004913/10000000000 : ℝ)|^17 ≤ (2227986327203/20000000000000 : ℝ)^13
        have hw : |(1867004913/10000000000 : ℝ)|=(1867004913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-183/2000000000 : ℝ)|^17 ≤ (2499/4000000000000 : ℝ)^13
        have hw : |(-183/2000000000 : ℝ)|=(183/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c307060_s1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((11793/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11793/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5899/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5899/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-88943/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-88943/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((8627/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8627/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(86771/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(86771/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-38659/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-38659/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4817/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4817/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4817/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4817/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base7 : ((1 : ℝ)*T) ≤ (92559/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base34 : ((-1 : ℝ)*N 0+(1 : ℝ)*P 0+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 0]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base43 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 2+(1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 1,f.sum]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (11793/12500 : ℝ) ^ (135/32 : ℝ) ≤ (39110727686312691111/50000000000000000000 : ℝ) := by
    have hpowers : (11793/12500 : ℝ)^135 ≤ (39110727686312691111/50000000000000000000 : ℝ)^32 := by
      have hnat : (11793 : ℕ)^135*50000000000000000000^32 ≤ 39110727686312691111^32*12500^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11793 12500 39110727686312691111 50000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11793/12500 : ℝ)) (X := (39110727686312691111/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (89110727686312691111/50000000000000000000 : ℝ) ≤ (5733988476184141/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (89110727686312691111/50000000000000000000 : ℝ)^32 ≤ (5733988476184141/5000000000000000 : ℝ)^135 := by
      have hnat : (89110727686312691111 : ℕ)^32*5000000000000000^135 ≤ 5733988476184141^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89110727686312691111 50000000000000000000 5733988476184141 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5733988476184141/5000000000000000 : ℝ)) (X := (89110727686312691111/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (64110727686312691111/25000000000000000000 : ℝ) ≤ (6250517097759709/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (64110727686312691111/25000000000000000000 : ℝ)^32 ≤ (6250517097759709/5000000000000000 : ℝ)^135 := by
      have hnat : (64110727686312691111 : ℕ)^32*5000000000000000^135 ≤ 6250517097759709^135*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64110727686312691111 25000000000000000000 6250517097759709 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (6250517097759709/5000000000000000 : ℝ)) (X := (64110727686312691111/25000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(733988476184141/4717200000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(10761012949491/98275000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (11793/12500 : ℝ)) (alpha := (733988476184141/4717200000000000 : ℝ)) (beta := (10761012949491/98275000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (11793/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(733988476184141/4717200000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(10761012949491/98275000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (5899/6250 : ℝ) ^ (135/32 : ℝ) ≤ (39180731503527031983/50000000000000000000 : ℝ) := by
    have hpowers : (5899/6250 : ℝ)^135 ≤ (39180731503527031983/50000000000000000000 : ℝ)^32 := by
      have hnat : (5899 : ℕ)^135*50000000000000000000^32 ≤ 39180731503527031983^32*6250^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5899 6250 39180731503527031983 50000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5899/6250 : ℝ)) (X := (39180731503527031983/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (89180731503527031983/50000000000000000000 : ℝ) ≤ (5735055894490089/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (89180731503527031983/50000000000000000000 : ℝ)^32 ≤ (5735055894490089/5000000000000000 : ℝ)^135 := by
      have hnat : (89180731503527031983 : ℕ)^32*5000000000000000^135 ≤ 5735055894490089^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        89180731503527031983 50000000000000000000 5735055894490089 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5735055894490089/5000000000000000 : ℝ)) (X := (89180731503527031983/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (64180731503527031983/25000000000000000000 : ℝ) ≤ (97689597158247/78125000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (64180731503527031983/25000000000000000000 : ℝ)^32 ≤ (97689597158247/78125000000000 : ℝ)^135 := by
      have hnat : (64180731503527031983 : ℕ)^32*78125000000000^135 ≤ 97689597158247^135*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64180731503527031983 25000000000000000000 97689597158247 78125000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (97689597158247/78125000000000 : ℝ)) (X := (64180731503527031983/25000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(735055894490089/4719200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(517078323637719/4719200000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (5899/6250 : ℝ)) (alpha := (735055894490089/4719200000000000 : ℝ)) (beta := (517078323637719/4719200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (5899/6250 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(735055894490089/4719200000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(517078323637719/4719200000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (88943/100000 : ℝ) ^ (135/32 : ℝ) ≤ (60997957927059559021/100000000000000000000 : ℝ) := by
    have hpowers : (88943/100000 : ℝ)^135 ≤ (60997957927059559021/100000000000000000000 : ℝ)^32 := by
      have hnat : (88943 : ℕ)^135*100000000000000000000^32 ≤ 60997957927059559021^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        88943 100000 60997957927059559021 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (88943/100000 : ℝ)) (X := (60997957927059559021/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (160997957927059559021/100000000000000000000 : ℝ) ≤ (2798749930441891/2500000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (160997957927059559021/100000000000000000000 : ℝ)^32 ≤ (2798749930441891/2500000000000000 : ℝ)^135 := by
      have hnat : (160997957927059559021 : ℕ)^32*2500000000000000^135 ≤ 2798749930441891^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        160997957927059559021 100000000000000000000 2798749930441891 2500000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2798749930441891/2500000000000000 : ℝ)) (X := (160997957927059559021/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (110997957927059559021/50000000000000000000 : ℝ) ≤ (12080824879461173/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (110997957927059559021/50000000000000000000 : ℝ)^32 ≤ (12080824879461173/10000000000000000 : ℝ)^135 := by
      have hnat : (110997957927059559021 : ℕ)^32*10000000000000000^135 ≤ 12080824879461173^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        110997957927059559021 50000000000000000000 12080824879461173 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12080824879461173/10000000000000000 : ℝ)) (X := (110997957927059559021/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(298749930441891/2223575000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(885825157693609/8894300000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (88943/100000 : ℝ)) (alpha := (298749930441891/2223575000000000 : ℝ)) (beta := (885825157693609/8894300000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (88943/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(298749930441891/2223575000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(885825157693609/8894300000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-809934267/5000000000 : ℝ)*X 0 0+(2231252157/5000000000 : ℝ)*X 0 1+(-256509839/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((446169057/1000000000 : ℝ)*X 1 0+(-1620209127/10000000000 : ℝ)*X 1 1+(-6413250749/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1067903151/10000000000 : ℝ)*X 0 0+(109871701/500000000 : ℝ)*X 0 1+(-4249786123/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((249867569/1000000000 : ℝ)*X 1 0+(-26227847/400000000 : ℝ)*X 1 1+(-4250120499/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((445176203/2000000000 : ℝ)*X 2 0+(8103532037/10000000000 : ℝ)*X 2 1+(215251417/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((2185566899/5000000000 : ℝ)*X 0 0+(7287562351/10000000000 : ℝ)*X 0 1+(-1727/10000000000 : ℝ)*X 0 2+(2185566899/5000000000 : ℝ)*X 1 0+(7287562351/10000000000 : ℝ)*X 1 1+(-1727/10000000000 : ℝ)*X 1 2+(2185566899/5000000000 : ℝ)*X 2 0+(7287562351/10000000000 : ℝ)*X 2 1+(-1727/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-1237593953/10000000000 : ℝ)*X 0 0+(106869039/625000000 : ℝ)*X 0 1+(-4358458893/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((133581663/1000000000 : ℝ)*X 1 0+(-404503457/2500000000 : ℝ)*X 1 1+(-8717603557/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((420048597/625000000 : ℝ)*X 2 0+(923058583/2500000000 : ℝ)*X 2 1+(1072287689/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((4427222557/5000000000 : ℝ)*X 0 0+(144319667/625000000 : ℝ)*X 0 1+(1313/10000000000 : ℝ)*X 0 2+(4427222557/5000000000 : ℝ)*X 1 0+(144319667/625000000 : ℝ)*X 1 1+(1313/10000000000 : ℝ)*X 1 2+(4427222557/5000000000 : ℝ)*X 2 0+(144319667/625000000 : ℝ)*X 2 1+(1313/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-325598507/2000000000 : ℝ)*X 0 0+(3519787827/10000000000 : ℝ)*X 0 1+(-900877761/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((1849190877/2500000000 : ℝ)*X 1 0+(-630544421/5000000000 : ℝ)*X 1 1+(-890251883/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((395350237/2000000000 : ℝ)*X 2 0+(7630129853/10000000000 : ℝ)*X 2 1+(2670336479/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((28551287/31250000 : ℝ)*X 0 0+(1867004913/10000000000 : ℝ)*X 0 1+(-183/2000000000 : ℝ)*X 0 2+(28551287/31250000 : ℝ)*X 1 0+(1867004913/10000000000 : ℝ)*X 1 1+(-183/2000000000 : ℝ)*X 1 2+(28551287/31250000 : ℝ)*X 2 0+(1867004913/10000000000 : ℝ)*X 2 1+(-183/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307060_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((8627/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8627/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2841289688852308206723953434013/206249646976700000000000000000000000 : ℝ) := by norm_num
    linear_combination (102906585249/250000000000 : ℝ)*(base5) + (459107526907/500000000000 : ℝ)*(base7) + (2112309/1000000000000 : ℝ)*(base43) + (516649/250000000000 : ℝ)*(base53) + (916592644343/500000000000 : ℝ)*(major_s1_0) + (229147897047/125000000000 : ℝ)*(major_s1_1) + (183318322209/100000000000 : ℝ)*(major_s1_2) + (7046579/500000000000 : ℝ)*(sp_s1_1) + (240059546551/125000000000 : ℝ)*(sp_s1_7) + (1920420921481/1000000000000 : ℝ)*(sp_s1_8) + (2332091071293/1000000000000 : ℝ)*(sp_s1_9) + (842940182887/500000000000 : ℝ)*(sp_s1_13) + (21735039/500000000000 : ℝ)*(sp_s1_15) + (13708707/1000000000000 : ℝ)*(sp_s1_23) + (235858330591/200000000000 : ℝ)*(f.failure) + (1920480551313/1000000000000 : ℝ)*(f.sum) + (6262468636126680271/52467475700000000000000000000000 : ℝ)*base62 + (548226928282743/889430000000000000000000000 : ℝ)*base64 + (116819824990867/589900000000000000000000000 : ℝ)*base66 + (27034342688417/88943000000000000000000000 : ℝ)*base69 + (22244045910199805371/209780959800000000000000000000000 : ℝ)*base70 + (6384245727891/24568750000000000000000000 : ℝ)*base72 + (44226254187603/589900000000000000000000000 : ℝ)*base75 + (2296052549729597/2358600000000000000000000000 : ℝ)*base76 + (350143341445824491/2318896900000000000000000000000 : ℝ)*base78 + (1279/2500000000000000 : ℝ)*base86 + (1221/2500000000000000 : ℝ)*base89 + (1279/2500000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(86771/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(86771/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1834310020880446963364854135041/206249646976700000000000000000000000 : ℝ) := by norm_num
    linear_combination (7299865259/7812500000 : ℝ)*(base7) + (78123/125000000000 : ℝ)*(base34) + (957/7812500000 : ℝ)*(base39) + (1097329/1000000000000 : ℝ)*(base53) + (906454221/10000000000 : ℝ)*(base60) + (430021415403/250000000000 : ℝ)*(major_s1_0) + (430021571649/250000000000 : ℝ)*(major_s1_1) + (430021297317/250000000000 : ℝ)*(major_s1_2) + (6393487/250000000000 : ℝ)*(sp_s1_8) + (1757062819191/1000000000000 : ℝ)*(sp_s1_14) + (1757037870227/1000000000000 : ℝ)*(sp_s1_15) + (27454133461/15625000000 : ℝ)*(sp_s1_16) + (2040876716191/1000000000000 : ℝ)*(sp_s1_20) + (40257453/1000000000000 : ℝ)*(sp_s1_27) + (276633711369/250000000000 : ℝ)*(f.failure) + (27454133461/15625000000 : ℝ)*(f.sum) + (41196561784265107979/104934951400000000000000000000000 : ℝ)*base63 + (1464706398483481/4447150000000000000000000000 : ℝ)*base64 + (523634930524129/1179800000000000000000000000 : ℝ)*base66 + (56608263843427/555893750000000000000000000 : ℝ)*base69 + (8736700419862448059/34963493300000000000000000000000 : ℝ)*base70 + (11251003131009/196550000000000000000000000 : ℝ)*base73 + (66379290700801/1179800000000000000000000000 : ℝ)*base75 + (97191827826449/393100000000000000000000000 : ℝ)*base76 + (53602510794203637/185511752000000000000000000000 : ℝ)*base79 + (1461/3125000000000000 : ℝ)*base86 + (1461/3125000000000000 : ℝ)*base88 + (2293/1562500000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-38659/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-38659/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (427222469284825338652726257/209869902800000000000000000000000 : ℝ) := by norm_num
    linear_combination (2461643911/3906250000 : ℝ)*(base7) + (878311/500000000000 : ℝ)*(base16) + (1781717/1000000000000 : ℝ)*(base34) + (94699358831/125000000000 : ℝ)*(base43) + (38950459799/25000000000 : ℝ)*(major_s1_0) + (800425303029/1000000000000 : ℝ)*(major_s1_1) + (1558020173677/1000000000000 : ℝ)*(major_s1_2) + (19640963/1000000000000 : ℝ)*(sp_s1_0) + (3692569/1000000000000 : ℝ)*(sp_s1_9) + (27268187/1000000000000 : ℝ)*(sp_s1_20) + (241821646249/250000000000 : ℝ)*(sp_s1_21) + (862450560851/500000000000 : ℝ)*(sp_s1_22) + (967304315107/1000000000000 : ℝ)*(sp_s1_23) + (1632429191907/1000000000000 : ℝ)*(sp_s1_27) + (200455480119/200000000000 : ℝ)*(f.failure) + (431225719581/250000000000 : ℝ)*(f.sum) + (233179093018758121901/419739805600000000000000000000000 : ℝ)*base62 + (5643931217747763/8894300000000000000000000000 : ℝ)*base64 + (578849817859091/4719200000000000000000000000 : ℝ)*base67 + (249032291886649/1111787500000000000000000000 : ℝ)*base68 + (28784378058104487731/104890479900000000000000000000000 : ℝ)*base71 + (794408467561/19655000000000000000000000 : ℝ)*base73 + (1186457811314179/4719200000000000000000000000 : ℝ)*base74 + (13343828944247/29482500000000000000000000 : ℝ)*base76 + (77877731517595999/18551175200000000000000000000000 : ℝ)*base78 + (211/2500000000000000 : ℝ)*base86 + (211/2500000000000000 : ℝ)*base88 + (211/2500000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((11793/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11793/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5899/6250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5899/6250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-88943/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-88943/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((8627/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(8627/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(86771/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(86771/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-38659/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-38659/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c307060_s1 p hpa hpb X hX hprev0

#print axioms solution
