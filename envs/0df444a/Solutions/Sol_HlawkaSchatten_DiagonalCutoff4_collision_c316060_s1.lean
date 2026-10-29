-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c316060_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:07:50.750249+00:00
-- url     : https://prove2.me/submissions/dbf5a561-a4fc-434b-b1c0-d29448ea03e6

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
theorem collision_support_c316060_s1_s1_0 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1888979581/10000000000 : ℝ)*x 0 + (4155490173/10000000000 : ℝ)*x 1 + (-6208972641/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1888979581/10000000000 : ℝ)^77 ≤ (2440142728757/20000000000000 : ℝ)^61 := by
    have hnat : (1888979581 : ℕ)^77*20000000000000^61 ≤ 2440142728757^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1888979581 10000000000 2440142728757 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4155490173/10000000000 : ℝ)^77 ≤ (33005685259527/100000000000000 : ℝ)^61 := by
    have hnat : (4155490173 : ℕ)^77*100000000000000^61 ≤ 33005685259527^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4155490173 10000000000 33005685259527 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6208972641/10000000000 : ℝ)^77 ≤ (54793601079057/100000000000000 : ℝ)^61 := by
    have hnat : (6208972641 : ℕ)^77*100000000000000^61 ≤ 54793601079057^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6208972641 10000000000 54793601079057 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1888979581/10000000000 : ℝ), (4155490173/10000000000 : ℝ), (-6208972641/10000000000 : ℝ)] ![(2440142728757/20000000000000 : ℝ), (33005685259527/100000000000000 : ℝ), (54793601079057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1888979581/10000000000 : ℝ)|^77 ≤ (2440142728757/20000000000000 : ℝ)^61
        have hw : |(-1888979581/10000000000 : ℝ)|=(1888979581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4155490173/10000000000 : ℝ)|^77 ≤ (33005685259527/100000000000000 : ℝ)^61
        have hw : |(4155490173/10000000000 : ℝ)|=(4155490173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6208972641/10000000000 : ℝ)|^77 ≤ (54793601079057/100000000000000 : ℝ)^61
        have hw : |(-6208972641/10000000000 : ℝ)|=(6208972641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316060_s1_s1_1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4489453439/10000000000 : ℝ)*x 0 + (-2214344827/10000000000 : ℝ)*x 1 + (-14138419/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4489453439/10000000000 : ℝ)^77 ≤ (36388615324267/100000000000000 : ℝ)^61 := by
    have hnat : (4489453439 : ℕ)^77*100000000000000^61 ≤ 36388615324267^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4489453439 10000000000 36388615324267 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2214344827/10000000000 : ℝ)^77 ≤ (14910983912533/100000000000000 : ℝ)^61 := by
    have hnat : (2214344827 : ℕ)^77*100000000000000^61 ≤ 14910983912533^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214344827 10000000000 14910983912533 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14138419/25000000 : ℝ)^77 ≤ (243502003749/500000000000 : ℝ)^61 := by
    have hnat : (14138419 : ℕ)^77*500000000000^61 ≤ 243502003749^61*25000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14138419 25000000 243502003749 500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4489453439/10000000000 : ℝ), (-2214344827/10000000000 : ℝ), (-14138419/25000000 : ℝ)] ![(36388615324267/100000000000000 : ℝ), (14910983912533/100000000000000 : ℝ), (243502003749/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4489453439/10000000000 : ℝ)|^77 ≤ (36388615324267/100000000000000 : ℝ)^61
        have hw : |(4489453439/10000000000 : ℝ)|=(4489453439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2214344827/10000000000 : ℝ)|^77 ≤ (14910983912533/100000000000000 : ℝ)^61
        have hw : |(-2214344827/10000000000 : ℝ)|=(2214344827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-14138419/25000000 : ℝ)|^77 ≤ (243502003749/500000000000 : ℝ)^61
        have hw : |(-14138419/25000000 : ℝ)|=(14138419/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316060_s1_s1_2 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (466817113/1000000000 : ℝ)*x 0 + (5881411319/10000000000 : ℝ)*x 1 + (1690213457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (466817113/1000000000 : ℝ)^77 ≤ (3822659302649/10000000000000 : ℝ)^61 := by
    have hnat : (466817113 : ℕ)^77*10000000000000^61 ≤ 3822659302649^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466817113 1000000000 3822659302649 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5881411319/10000000000 : ℝ)^77 ≤ (51170268769639/100000000000000 : ℝ)^61 := by
    have hnat : (5881411319 : ℕ)^77*100000000000000^61 ≤ 51170268769639^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5881411319 10000000000 51170268769639 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1690213457/10000000000 : ℝ)^77 ≤ (2120627640207/20000000000000 : ℝ)^61 := by
    have hnat : (1690213457 : ℕ)^77*20000000000000^61 ≤ 2120627640207^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1690213457 10000000000 2120627640207 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(466817113/1000000000 : ℝ), (5881411319/10000000000 : ℝ), (1690213457/10000000000 : ℝ)] ![(3822659302649/10000000000000 : ℝ), (51170268769639/100000000000000 : ℝ), (2120627640207/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(466817113/1000000000 : ℝ)|^77 ≤ (3822659302649/10000000000000 : ℝ)^61
        have hw : |(466817113/1000000000 : ℝ)|=(466817113/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5881411319/10000000000 : ℝ)|^77 ≤ (51170268769639/100000000000000 : ℝ)^61
        have hw : |(5881411319/10000000000 : ℝ)|=(5881411319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1690213457/10000000000 : ℝ)|^77 ≤ (2120627640207/20000000000000 : ℝ)^61
        have hw : |(1690213457/10000000000 : ℝ)|=(1690213457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316060_s1_s1_7 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-858606833/5000000000 : ℝ)*x 0 + (158888181/400000000 : ℝ)*x 1 + (-6495436429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (858606833/5000000000 : ℝ)^77 ≤ (5408695434761/50000000000000 : ℝ)^61 := by
    have hnat : (858606833 : ℕ)^77*50000000000000^61 ≤ 5408695434761^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      858606833 5000000000 5408695434761 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (158888181/400000000 : ℝ)^77 ≤ (7794702992851/25000000000000 : ℝ)^61 := by
    have hnat : (158888181 : ℕ)^77*25000000000000^61 ≤ 7794702992851^61*400000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158888181 400000000 7794702992851 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6495436429/10000000000 : ℝ)^77 ≤ (29001898569527/50000000000000 : ℝ)^61 := by
    have hnat : (6495436429 : ℕ)^77*50000000000000^61 ≤ 29001898569527^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6495436429 10000000000 29001898569527 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-858606833/5000000000 : ℝ), (158888181/400000000 : ℝ), (-6495436429/10000000000 : ℝ)] ![(5408695434761/50000000000000 : ℝ), (7794702992851/25000000000000 : ℝ), (29001898569527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-858606833/5000000000 : ℝ)|^77 ≤ (5408695434761/50000000000000 : ℝ)^61
        have hw : |(-858606833/5000000000 : ℝ)|=(858606833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(158888181/400000000 : ℝ)|^77 ≤ (7794702992851/25000000000000 : ℝ)^61
        have hw : |(158888181/400000000 : ℝ)|=(158888181/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6495436429/10000000000 : ℝ)|^77 ≤ (29001898569527/50000000000000 : ℝ)^61
        have hw : |(-6495436429/10000000000 : ℝ)|=(6495436429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316060_s1_s1_8 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2109727163/5000000000 : ℝ)*x 0 + (-1406790929/10000000000 : ℝ)*x 1 + (-1622474309/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109727163/5000000000 : ℝ)^77 ≤ (16824139566183/50000000000000 : ℝ)^61 := by
    have hnat : (2109727163 : ℕ)^77*50000000000000^61 ≤ 16824139566183^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109727163 5000000000 16824139566183 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1406790929/10000000000 : ℝ)^77 ≤ (8410355659687/100000000000000 : ℝ)^61 := by
    have hnat : (1406790929 : ℕ)^77*100000000000000^61 ≤ 8410355659687^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1406790929 10000000000 8410355659687 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1622474309/2500000000 : ℝ)^77 ≤ (57941365190289/100000000000000 : ℝ)^61 := by
    have hnat : (1622474309 : ℕ)^77*100000000000000^61 ≤ 57941365190289^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1622474309 2500000000 57941365190289 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2109727163/5000000000 : ℝ), (-1406790929/10000000000 : ℝ), (-1622474309/2500000000 : ℝ)] ![(16824139566183/50000000000000 : ℝ), (8410355659687/100000000000000 : ℝ), (57941365190289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2109727163/5000000000 : ℝ)|^77 ≤ (16824139566183/50000000000000 : ℝ)^61
        have hw : |(2109727163/5000000000 : ℝ)|=(2109727163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1406790929/10000000000 : ℝ)|^77 ≤ (8410355659687/100000000000000 : ℝ)^61
        have hw : |(-1406790929/10000000000 : ℝ)|=(1406790929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1622474309/2500000000 : ℝ)|^77 ≤ (57941365190289/100000000000000 : ℝ)^61
        have hw : |(-1622474309/2500000000 : ℝ)|=(1622474309/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316060_s1_s1_9 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (219980417/500000000 : ℝ)*x 0 + (6640464519/10000000000 : ℝ)*x 1 + (914740401/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219980417/500000000 : ℝ)^77 ≤ (7094360650091/20000000000000 : ℝ)^61 := by
    have hnat : (219980417 : ℕ)^77*20000000000000^61 ≤ 7094360650091^61*500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219980417 500000000 7094360650091 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6640464519/10000000000 : ℝ)^77 ≤ (3727709054001/6250000000000 : ℝ)^61 := by
    have hnat : (6640464519 : ℕ)^77*6250000000000^61 ≤ 3727709054001^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6640464519 10000000000 3727709054001 6250000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (914740401/10000000000 : ℝ)^77 ≤ (4884851864899/100000000000000 : ℝ)^61 := by
    have hnat : (914740401 : ℕ)^77*100000000000000^61 ≤ 4884851864899^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914740401 10000000000 4884851864899 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(219980417/500000000 : ℝ), (6640464519/10000000000 : ℝ), (914740401/10000000000 : ℝ)] ![(7094360650091/20000000000000 : ℝ), (3727709054001/6250000000000 : ℝ), (4884851864899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(219980417/500000000 : ℝ)|^77 ≤ (7094360650091/20000000000000 : ℝ)^61
        have hw : |(219980417/500000000 : ℝ)|=(219980417/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6640464519/10000000000 : ℝ)|^77 ≤ (3727709054001/6250000000000 : ℝ)^61
        have hw : |(6640464519/10000000000 : ℝ)|=(6640464519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(914740401/10000000000 : ℝ)|^77 ≤ (4884851864899/100000000000000 : ℝ)^61
        have hw : |(914740401/10000000000 : ℝ)|=(914740401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316060_s1_s1_13 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (663438773/1000000000 : ℝ)*x 0 + (2430094401/5000000000 : ℝ)*x 1 + (-7376931/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663438773/1000000000 : ℝ)^77 ≤ (59574456409609/100000000000000 : ℝ)^61 := by
    have hnat : (663438773 : ℕ)^77*100000000000000^61 ≤ 59574456409609^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663438773 1000000000 59574456409609 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2430094401/5000000000 : ℝ)^77 ≤ (40222012836053/100000000000000 : ℝ)^61 := by
    have hnat : (2430094401 : ℕ)^77*100000000000000^61 ≤ 40222012836053^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2430094401 5000000000 40222012836053 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (7376931/1000000000 : ℝ)^77 ≤ (203530738713/100000000000000 : ℝ)^61 := by
    have hnat : (7376931 : ℕ)^77*100000000000000^61 ≤ 203530738713^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7376931 1000000000 203530738713 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663438773/1000000000 : ℝ), (2430094401/5000000000 : ℝ), (-7376931/1000000000 : ℝ)] ![(59574456409609/100000000000000 : ℝ), (40222012836053/100000000000000 : ℝ), (203530738713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663438773/1000000000 : ℝ)|^77 ≤ (59574456409609/100000000000000 : ℝ)^61
        have hw : |(663438773/1000000000 : ℝ)|=(663438773/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2430094401/5000000000 : ℝ)|^77 ≤ (40222012836053/100000000000000 : ℝ)^61
        have hw : |(2430094401/5000000000 : ℝ)|=(2430094401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-7376931/1000000000 : ℝ)|^77 ≤ (203530738713/100000000000000 : ℝ)^61
        have hw : |(-7376931/1000000000 : ℝ)|=(7376931/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316060_s1_s1_14 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1105664059/10000000000 : ℝ)*x 0 + (2219335669/5000000000 : ℝ)*x 1 + (-1622106257/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1105664059/10000000000 : ℝ)^77 ≤ (1551351707739/25000000000000 : ℝ)^61 := by
    have hnat : (1105664059 : ℕ)^77*25000000000000^61 ≤ 1551351707739^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105664059 10000000000 1551351707739 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2219335669/5000000000 : ℝ)^77 ≤ (35869818784707/100000000000000 : ℝ)^61 := by
    have hnat : (2219335669 : ℕ)^77*100000000000000^61 ≤ 35869818784707^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2219335669 5000000000 35869818784707 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1622106257/2500000000 : ℝ)^77 ≤ (28962387181433/50000000000000 : ℝ)^61 := by
    have hnat : (1622106257 : ℕ)^77*50000000000000^61 ≤ 28962387181433^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1622106257 2500000000 28962387181433 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1105664059/10000000000 : ℝ), (2219335669/5000000000 : ℝ), (-1622106257/2500000000 : ℝ)] ![(1551351707739/25000000000000 : ℝ), (35869818784707/100000000000000 : ℝ), (28962387181433/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1105664059/10000000000 : ℝ)|^77 ≤ (1551351707739/25000000000000 : ℝ)^61
        have hw : |(-1105664059/10000000000 : ℝ)|=(1105664059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2219335669/5000000000 : ℝ)|^77 ≤ (35869818784707/100000000000000 : ℝ)^61
        have hw : |(2219335669/5000000000 : ℝ)|=(2219335669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1622106257/2500000000 : ℝ)|^77 ≤ (28962387181433/50000000000000 : ℝ)^61
        have hw : |(-1622106257/2500000000 : ℝ)|=(1622106257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316060_s1_s1_15 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (422593797/1000000000 : ℝ)*x 0 + (-704304101/5000000000 : ℝ)*x 1 + (-6482886689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (422593797/1000000000 : ℝ)^77 ≤ (1685677911159/5000000000000 : ℝ)^61 := by
    have hnat : (422593797 : ℕ)^77*5000000000000^61 ≤ 1685677911159^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422593797 1000000000 1685677911159 5000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (704304101/5000000000 : ℝ)^77 ≤ (4212036018337/50000000000000 : ℝ)^61 := by
    have hnat : (704304101 : ℕ)^77*50000000000000^61 ≤ 4212036018337^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      704304101 5000000000 4212036018337 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6482886689/10000000000 : ℝ)^77 ≤ (57862369726661/100000000000000 : ℝ)^61 := by
    have hnat : (6482886689 : ℕ)^77*100000000000000^61 ≤ 57862369726661^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6482886689 10000000000 57862369726661 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(422593797/1000000000 : ℝ), (-704304101/5000000000 : ℝ), (-6482886689/10000000000 : ℝ)] ![(1685677911159/5000000000000 : ℝ), (4212036018337/50000000000000 : ℝ), (57862369726661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(422593797/1000000000 : ℝ)|^77 ≤ (1685677911159/5000000000000 : ℝ)^61
        have hw : |(422593797/1000000000 : ℝ)|=(422593797/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-704304101/5000000000 : ℝ)|^77 ≤ (4212036018337/50000000000000 : ℝ)^61
        have hw : |(-704304101/5000000000 : ℝ)|=(704304101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6482886689/10000000000 : ℝ)|^77 ≤ (57862369726661/100000000000000 : ℝ)^61
        have hw : |(-6482886689/10000000000 : ℝ)|=(6482886689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316060_s1_s1_16 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2752102091/5000000000 : ℝ)*x 0 + (5591280001/10000000000 : ℝ)*x 1 + (92175103/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2752102091/5000000000 : ℝ)^77 ≤ (47063041230921/100000000000000 : ℝ)^61 := by
    have hnat : (2752102091 : ℕ)^77*100000000000000^61 ≤ 47063041230921^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2752102091 5000000000 47063041230921 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5591280001/10000000000 : ℝ)^77 ≤ (24002400950823/50000000000000 : ℝ)^61 := by
    have hnat : (5591280001 : ℕ)^77*50000000000000^61 ≤ 24002400950823^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5591280001 10000000000 24002400950823 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (92175103/1000000000 : ℝ)^77 ≤ (4932156848203/100000000000000 : ℝ)^61 := by
    have hnat : (92175103 : ℕ)^77*100000000000000^61 ≤ 4932156848203^61*1000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      92175103 1000000000 4932156848203 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2752102091/5000000000 : ℝ), (5591280001/10000000000 : ℝ), (92175103/1000000000 : ℝ)] ![(47063041230921/100000000000000 : ℝ), (24002400950823/50000000000000 : ℝ), (4932156848203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2752102091/5000000000 : ℝ)|^77 ≤ (47063041230921/100000000000000 : ℝ)^61
        have hw : |(2752102091/5000000000 : ℝ)|=(2752102091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5591280001/10000000000 : ℝ)|^77 ≤ (24002400950823/50000000000000 : ℝ)^61
        have hw : |(5591280001/10000000000 : ℝ)|=(5591280001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(92175103/1000000000 : ℝ)|^77 ≤ (4932156848203/100000000000000 : ℝ)^61
        have hw : |(92175103/1000000000 : ℝ)|=(92175103/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316060_s1_s1_20 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1968188849/2500000000 : ℝ)*x 0 + (3418029533/10000000000 : ℝ)*x 1 + (-91611451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1968188849/2500000000 : ℝ)^77 ≤ (14788063728177/20000000000000 : ℝ)^61 := by
    have hnat : (1968188849 : ℕ)^77*20000000000000^61 ≤ 14788063728177^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1968188849 2500000000 14788063728177 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3418029533/10000000000 : ℝ)^77 ≤ (2579214721389/10000000000000 : ℝ)^61 := by
    have hnat : (3418029533 : ℕ)^77*10000000000000^61 ≤ 2579214721389^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3418029533 10000000000 2579214721389 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (91611451/10000000000 : ℝ)^77 ≤ (267534138393/100000000000000 : ℝ)^61 := by
    have hnat : (91611451 : ℕ)^77*100000000000000^61 ≤ 267534138393^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      91611451 10000000000 267534138393 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1968188849/2500000000 : ℝ), (3418029533/10000000000 : ℝ), (-91611451/10000000000 : ℝ)] ![(14788063728177/20000000000000 : ℝ), (2579214721389/10000000000000 : ℝ), (267534138393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1968188849/2500000000 : ℝ)|^77 ≤ (14788063728177/20000000000000 : ℝ)^61
        have hw : |(1968188849/2500000000 : ℝ)|=(1968188849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3418029533/10000000000 : ℝ)|^77 ≤ (2579214721389/10000000000000 : ℝ)^61
        have hw : |(3418029533/10000000000 : ℝ)|=(3418029533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-91611451/10000000000 : ℝ)|^77 ≤ (267534138393/100000000000000 : ℝ)^61
        have hw : |(-91611451/10000000000 : ℝ)|=(91611451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316060_s1_s1_21 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-400717037/5000000000 : ℝ)*x 0 + (1315886421/2500000000 : ℝ)*x 1 + (-236039933/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (400717037/5000000000 : ℝ)^77 ≤ (4133878601209/100000000000000 : ℝ)^61 := by
    have hnat : (400717037 : ℕ)^77*100000000000000^61 ≤ 4133878601209^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400717037 5000000000 4133878601209 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315886421/2500000000 : ℝ)^77 ≤ (69501010163/156250000000 : ℝ)^61 := by
    have hnat : (1315886421 : ℕ)^77*156250000000^61 ≤ 69501010163^61*2500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315886421 2500000000 69501010163 156250000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (236039933/400000000 : ℝ)^77 ≤ (51385474870643/100000000000000 : ℝ)^61 := by
    have hnat : (236039933 : ℕ)^77*100000000000000^61 ≤ 51385474870643^61*400000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      236039933 400000000 51385474870643 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-400717037/5000000000 : ℝ), (1315886421/2500000000 : ℝ), (-236039933/400000000 : ℝ)] ![(4133878601209/100000000000000 : ℝ), (69501010163/156250000000 : ℝ), (51385474870643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-400717037/5000000000 : ℝ)|^77 ≤ (4133878601209/100000000000000 : ℝ)^61
        have hw : |(-400717037/5000000000 : ℝ)|=(400717037/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315886421/2500000000 : ℝ)|^77 ≤ (69501010163/156250000000 : ℝ)^61
        have hw : |(1315886421/2500000000 : ℝ)|=(1315886421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-236039933/400000000 : ℝ)|^77 ≤ (51385474870643/100000000000000 : ℝ)^61
        have hw : |(-236039933/400000000 : ℝ)|=(236039933/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316060_s1_s1_22 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5628280767/10000000000 : ℝ)*x 0 + (-1157501/10000000 : ℝ)*x 1 + (-5313947751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5628280767/10000000000 : ℝ)^77 ≤ (48406149978697/100000000000000 : ℝ)^61 := by
    have hnat : (5628280767 : ℕ)^77*100000000000000^61 ≤ 48406149978697^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5628280767 10000000000 48406149978697 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1157501/10000000 : ℝ)^77 ≤ (1314975413671/20000000000000 : ℝ)^61 := by
    have hnat : (1157501 : ℕ)^77*20000000000000^61 ≤ 1314975413671^61*10000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1157501 10000000 1314975413671 20000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5313947751/10000000000 : ℝ)^77 ≤ (2250948647247/5000000000000 : ℝ)^61 := by
    have hnat : (5313947751 : ℕ)^77*5000000000000^61 ≤ 2250948647247^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5313947751 10000000000 2250948647247 5000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5628280767/10000000000 : ℝ), (-1157501/10000000 : ℝ), (-5313947751/10000000000 : ℝ)] ![(48406149978697/100000000000000 : ℝ), (1314975413671/20000000000000 : ℝ), (2250948647247/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5628280767/10000000000 : ℝ)|^77 ≤ (48406149978697/100000000000000 : ℝ)^61
        have hw : |(5628280767/10000000000 : ℝ)|=(5628280767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1157501/10000000 : ℝ)|^77 ≤ (1314975413671/20000000000000 : ℝ)^61
        have hw : |(-1157501/10000000 : ℝ)|=(1157501/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5313947751/10000000000 : ℝ)|^77 ≤ (2250948647247/5000000000000 : ℝ)^61
        have hw : |(-5313947751/10000000000 : ℝ)|=(5313947751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316060_s1_s1_23 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (212763607/500000000 : ℝ)*x 0 + (318567011/500000000 : ℝ)*x 1 + (1534104799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212763607/500000000 : ℝ)^77 ≤ (34009230549567/100000000000000 : ℝ)^61 := by
    have hnat : (212763607 : ℕ)^77*100000000000000^61 ≤ 34009230549567^61*500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212763607 500000000 34009230549567 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (318567011/500000000 : ℝ)^77 ≤ (5660848043099/10000000000000 : ℝ)^61 := by
    have hnat : (318567011 : ℕ)^77*10000000000000^61 ≤ 5660848043099^61*500000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318567011 500000000 5660848043099 10000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1534104799/10000000000 : ℝ)^77 ≤ (2345572251079/25000000000000 : ℝ)^61 := by
    have hnat : (1534104799 : ℕ)^77*25000000000000^61 ≤ 2345572251079^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1534104799 10000000000 2345572251079 25000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212763607/500000000 : ℝ), (318567011/500000000 : ℝ), (1534104799/10000000000 : ℝ)] ![(34009230549567/100000000000000 : ℝ), (5660848043099/10000000000000 : ℝ), (2345572251079/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212763607/500000000 : ℝ)|^77 ≤ (34009230549567/100000000000000 : ℝ)^61
        have hw : |(212763607/500000000 : ℝ)|=(212763607/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(318567011/500000000 : ℝ)|^77 ≤ (5660848043099/10000000000000 : ℝ)^61
        have hw : |(318567011/500000000 : ℝ)|=(318567011/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1534104799/10000000000 : ℝ)|^77 ≤ (2345572251079/25000000000000 : ℝ)^61
        have hw : |(1534104799/10000000000 : ℝ)|=(1534104799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c316060_s1_s1_27 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4128305973/5000000000 : ℝ)*x 0 + (2892984637/10000000000 : ℝ)*x 1 + (-680427/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4128305973/5000000000 : ℝ)^77 ≤ (39259920744723/50000000000000 : ℝ)^61 := by
    have hnat : (4128305973 : ℕ)^77*50000000000000^61 ≤ 39259920744723^61*5000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128305973 5000000000 39259920744723 50000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2892984637/10000000000 : ℝ)^77 ≤ (2611980189353/12500000000000 : ℝ)^61 := by
    have hnat : (2892984637 : ℕ)^77*12500000000000^61 ≤ 2611980189353^61*10000000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2892984637 10000000000 2611980189353 12500000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (680427/40000000 : ℝ)^77 ≤ (584316984667/100000000000000 : ℝ)^61 := by
    have hnat : (680427 : ℕ)^77*100000000000000^61 ≤ 584316984667^61*40000000^77 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680427 40000000 584316984667 100000000000000 77 61 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (77/16 : ℝ)) 77 61 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4128305973/5000000000 : ℝ), (2892984637/10000000000 : ℝ), (-680427/40000000 : ℝ)] ![(39259920744723/50000000000000 : ℝ), (2611980189353/12500000000000 : ℝ), (584316984667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4128305973/5000000000 : ℝ)|^77 ≤ (39259920744723/50000000000000 : ℝ)^61
        have hw : |(4128305973/5000000000 : ℝ)|=(4128305973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2892984637/10000000000 : ℝ)|^77 ≤ (2611980189353/12500000000000 : ℝ)^61
        have hw : |(2892984637/10000000000 : ℝ)|=(2892984637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-680427/40000000 : ℝ)|^77 ≤ (584316984667/100000000000000 : ℝ)^61
        have hw : |(-680427/40000000 : ℝ)|=(680427/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c316060_s1 (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((1583/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1583/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(78761/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(78761/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-17429/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-17429/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((11829/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11829/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(52251/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(52251/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8959/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-8959/25000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (1587/2000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (1587/2000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (1587/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (1587/2000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base12 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).1]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (1583/2000 : ℝ) ^ (19/4 : ℝ) ≤ (514590651538573199/1562500000000000000 : ℝ) := by
    have hpowers : (1583/2000 : ℝ)^19 ≤ (514590651538573199/1562500000000000000 : ℝ)^4 := by
      have hnat : (1583 : ℕ)^19*1562500000000000000^4 ≤ 514590651538573199^4*2000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1583 2000 514590651538573199 1562500000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1583/2000 : ℝ)) (X := (514590651538573199/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0a : (2077090651538573199/1562500000000000000 : ℝ) ≤ (10617652576203703/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (2077090651538573199/1562500000000000000 : ℝ)^4 ≤ (10617652576203703/10000000000000000 : ℝ)^19 := by
      have hnat : (2077090651538573199 : ℕ)^4*10000000000000000^19 ≤ 10617652576203703^19*1562500000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2077090651538573199 1562500000000000000 10617652576203703 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10617652576203703/10000000000000000 : ℝ)) (X := (2077090651538573199/1562500000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner0b : (1295840651538573199/781250000000000000 : ℝ) ≤ (11124118168417019/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (1295840651538573199/781250000000000000 : ℝ)^4 ≤ (11124118168417019/10000000000000000 : ℝ)^19 := by
      have hnat : (1295840651538573199 : ℕ)^4*10000000000000000^19 ≤ 11124118168417019^19*781250000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1295840651538573199 781250000000000000 11124118168417019 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11124118168417019/10000000000000000 : ℝ)) (X := (1295840651538573199/781250000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(617652576203703/7915000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(126616398053329/1978750000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (1583/2000 : ℝ)) (alpha := (617652576203703/7915000000000000 : ℝ)) (beta := (126616398053329/1978750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (1583/2000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(617652576203703/7915000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(126616398053329/1978750000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (78761/100000 : ℝ) ^ (19/4 : ℝ) ≤ (64344035925439411/200000000000000000 : ℝ) := by
    have hpowers : (78761/100000 : ℝ)^19 ≤ (64344035925439411/200000000000000000 : ℝ)^4 := by
      have hnat : (78761 : ℕ)^19*200000000000000000^4 ≤ 64344035925439411^4*100000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        78761 100000 64344035925439411 200000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (78761/100000 : ℝ)) (X := (64344035925439411/200000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1a : (264344035925439411/200000000000000000 : ℝ) ≤ (5302407015327831/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (264344035925439411/200000000000000000 : ℝ)^4 ≤ (5302407015327831/5000000000000000 : ℝ)^19 := by
      have hnat : (264344035925439411 : ℕ)^4*5000000000000000^19 ≤ 5302407015327831^19*200000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        264344035925439411 200000000000000000 5302407015327831 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5302407015327831/5000000000000000 : ℝ)) (X := (264344035925439411/200000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner1b : (164344035925439411/100000000000000000 : ℝ) ≤ (1110252817104773/1000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (164344035925439411/100000000000000000 : ℝ)^4 ≤ (1110252817104773/1000000000000000 : ℝ)^19 := by
      have hnat : (164344035925439411 : ℕ)^4*1000000000000000^19 ≤ 1110252817104773^19*100000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        164344035925439411 100000000000000000 1110252817104773 1000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1110252817104773/1000000000000000 : ℝ)) (X := (164344035925439411/100000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(302407015327831/3938050000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(7319325594001/115825000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (78761/100000 : ℝ)) (alpha := (302407015327831/3938050000000000 : ℝ)) (beta := (7319325594001/115825000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (78761/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(302407015327831/3938050000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(7319325594001/115825000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (17429/25000 : ℝ) ^ (19/4 : ℝ) ≤ (9011543743425838329/50000000000000000000 : ℝ) := by
    have hpowers : (17429/25000 : ℝ)^19 ≤ (9011543743425838329/50000000000000000000 : ℝ)^4 := by
      have hnat : (17429 : ℕ)^19*50000000000000000000^4 ≤ 9011543743425838329^4*25000^19 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17429 25000 9011543743425838329 50000000000000000000 19 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17429/25000 : ℝ)) (X := (9011543743425838329/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2a : (59011543743425838329/50000000000000000000 : ℝ) ≤ (10355019984522707/10000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (59011543743425838329/50000000000000000000 : ℝ)^4 ≤ (10355019984522707/10000000000000000 : ℝ)^19 := by
      have hnat : (59011543743425838329 : ℕ)^4*10000000000000000^19 ≤ 10355019984522707^19*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59011543743425838329 50000000000000000000 10355019984522707 10000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10355019984522707/10000000000000000 : ℝ)) (X := (59011543743425838329/50000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have s1_corner2b : (34011543743425838329/25000000000000000000 : ℝ) ≤ (5334755208265969/5000000000000000 : ℝ) ^ (19/4 : ℝ) := by
    have hpowers : (34011543743425838329/25000000000000000000 : ℝ)^4 ≤ (5334755208265969/5000000000000000 : ℝ)^19 := by
      have hnat : (34011543743425838329 : ℕ)^4*5000000000000000^19 ≤ 5334755208265969^19*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34011543743425838329 25000000000000000000 5334755208265969 5000000000000000 4 19 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5334755208265969/5000000000000000 : ℝ)) (X := (34011543743425838329/25000000000000000000 : ℝ)) (by norm_num) 19 4 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(355019984522707/6971600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(314490432009231/6971600000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (19/4 : ℝ)) (rho := (17429/25000 : ℝ)) (alpha := (355019984522707/6971600000000000 : ℝ)) (beta := (314490432009231/6971600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (17429/25000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(355019984522707/6971600000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(314490432009231/6971600000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1888979581/10000000000 : ℝ)*X 0 0+(4155490173/10000000000 : ℝ)*X 0 1+(-6208972641/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316060_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4489453439/10000000000 : ℝ)*X 1 0+(-2214344827/10000000000 : ℝ)*X 1 1+(-14138419/25000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316060_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((466817113/1000000000 : ℝ)*X 2 0+(5881411319/10000000000 : ℝ)*X 2 1+(1690213457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316060_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-858606833/5000000000 : ℝ)*X 0 0+(158888181/400000000 : ℝ)*X 0 1+(-6495436429/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316060_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((2109727163/5000000000 : ℝ)*X 1 0+(-1406790929/10000000000 : ℝ)*X 1 1+(-1622474309/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316060_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((219980417/500000000 : ℝ)*X 2 0+(6640464519/10000000000 : ℝ)*X 2 1+(914740401/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316060_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((663438773/1000000000 : ℝ)*X 0 0+(2430094401/5000000000 : ℝ)*X 0 1+(-7376931/1000000000 : ℝ)*X 0 2+(663438773/1000000000 : ℝ)*X 1 0+(2430094401/5000000000 : ℝ)*X 1 1+(-7376931/1000000000 : ℝ)*X 1 2+(663438773/1000000000 : ℝ)*X 2 0+(2430094401/5000000000 : ℝ)*X 2 1+(-7376931/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316060_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-1105664059/10000000000 : ℝ)*X 0 0+(2219335669/5000000000 : ℝ)*X 0 1+(-1622106257/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316060_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((422593797/1000000000 : ℝ)*X 1 0+(-704304101/5000000000 : ℝ)*X 1 1+(-6482886689/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316060_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((2752102091/5000000000 : ℝ)*X 2 0+(5591280001/10000000000 : ℝ)*X 2 1+(92175103/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316060_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1968188849/2500000000 : ℝ)*X 0 0+(3418029533/10000000000 : ℝ)*X 0 1+(-91611451/10000000000 : ℝ)*X 0 2+(1968188849/2500000000 : ℝ)*X 1 0+(3418029533/10000000000 : ℝ)*X 1 1+(-91611451/10000000000 : ℝ)*X 1 2+(1968188849/2500000000 : ℝ)*X 2 0+(3418029533/10000000000 : ℝ)*X 2 1+(-91611451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316060_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-400717037/5000000000 : ℝ)*X 0 0+(1315886421/2500000000 : ℝ)*X 0 1+(-236039933/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c316060_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((5628280767/10000000000 : ℝ)*X 1 0+(-1157501/10000000 : ℝ)*X 1 1+(-5313947751/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c316060_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((212763607/500000000 : ℝ)*X 2 0+(318567011/500000000 : ℝ)*X 2 1+(1534104799/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c316060_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((4128305973/5000000000 : ℝ)*X 0 0+(2892984637/10000000000 : ℝ)*X 0 1+(-680427/40000000 : ℝ)*X 0 2+(4128305973/5000000000 : ℝ)*X 1 0+(2892984637/10000000000 : ℝ)*X 1 1+(-680427/40000000 : ℝ)*X 1 2+(4128305973/5000000000 : ℝ)*X 2 0+(2892984637/10000000000 : ℝ)*X 2 1+(-680427/40000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c316060_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((11829/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11829/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (678892895853790219280485990443/42441883152871093750000000000000000 : ℝ) := by norm_num
    linear_combination (11288949/1000000000000 : ℝ)*(base5) + (2738951/250000000000 : ℝ)*(base39) + (104999/50000000000 : ℝ)*(base49) + (184387968201/250000000000 : ℝ)*(base59) + (6683533777633/1000000000000 : ℝ)*(major_s1_0) + (6683533777633/1000000000000 : ℝ)*(major_s1_1) + (6683533777633/1000000000000 : ℝ)*(major_s1_2) + (1752357/20000000000 : ℝ)*(sp_s1_1) + (4798224075161/500000000000 : ℝ)*(sp_s1_7) + (1919288310057/200000000000 : ℝ)*(sp_s1_8) + (9596340395047/1000000000000 : ℝ)*(sp_s1_9) + (1885260883119/500000000000 : ℝ)*(sp_s1_13) + (81017813/1000000000000 : ℝ)*(sp_s1_14) + (200062037/1000000000000 : ℝ)*(sp_s1_23) + (3770533055187/1000000000000 : ℝ)*(f.failure) + (1919305833627/200000000000 : ℝ)*(f.sum) + (155492002629294707067/549090187600000000000000000000000 : ℝ)*base63 + (880577344994577/6971600000000000000000000000 : ℝ)*base65 + (729028523199/57912500000000000000000000 : ℝ)*base67 + (1919913719004531/6971600000000000000000000000 : ℝ)*base69 + (28654906046723312917/275901070000000000000000000000000 : ℝ)*base71 + (904030072305257/1978750000000000000000000000 : ℝ)*base73 + (490346870279523/3938050000000000000000000000 : ℝ)*base75 + (149362888548501/7915000000000000000000000000 : ℝ)*base76 + (3178697047965066381/9167548750000000000000000000000 : ℝ)*base79 + (17941/100000000000000000 : ℝ)*base86 + (17941/100000000000000000 : ℝ)*base88 + (17941/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(52251/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(52251/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13326471656010916873563299558511/1086512208713500000000000000000000000 : ℝ) := by norm_num
    linear_combination (3881637/1000000000000 : ℝ)*(base12) + (209849051/781250000 : ℝ)*(base59) + (634226574989/100000000000 : ℝ)*(major_s1_0) + (634226574989/100000000000 : ℝ)*(major_s1_1) + (634226574989/100000000000 : ℝ)*(major_s1_2) + (4035951/500000000000 : ℝ)*(sp_s1_1) + (5582443/500000000000 : ℝ)*(sp_s1_2) + (17946529/250000000000 : ℝ)*(sp_s1_7) + (805395771/200000000000 : ℝ)*(sp_s1_8) + (9106445938497/1000000000000 : ℝ)*(sp_s1_14) + (2275621638873/250000000000 : ℝ)*(sp_s1_15) + (2276627610341/250000000000 : ℝ)*(sp_s1_16) + (3577899476077/1000000000000 : ℝ)*(sp_s1_20) + (106328991/1000000000000 : ℝ)*(sp_s1_27) + (894501451267/250000000000 : ℝ)*(f.failure) + (1457043457/160000000 : ℝ)*(f.sum) + (23469239282706066267/54909018760000000000000000000000 : ℝ)*base63 + (158904467420363/697160000000000000000000000 : ℝ)*base64 + (4628346284837/46330000000000000000000000 : ℝ)*base67 + (374613969362207/697160000000000000000000000 : ℝ)*base69 + (1987464429562466661/27590107000000000000000000000000 : ℝ)*base71 + (139678886024863/395750000000000000000000000 : ℝ)*base72 + (10533722458469/98451250000000000000000000 : ℝ)*base75 + (126173846085633/791500000000000000000000000 : ℝ)*base76 + (126106731916876829/1833509750000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (15381/25000000000000000 : ℝ)*base86 + (15381/25000000000000000 : ℝ)*base88 + (15381/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8959/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-8959/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1532300288222307668766552198807/319562414327500000000000000000000000 : ℝ) := by norm_num
    linear_combination (5389991/1000000000000 : ℝ)*(base11) + (17397/1000000000000 : ℝ)*(base15) + (374403363517/1000000000000 : ℝ)*(base39) + (161052858939/1000000000000 : ℝ)*(base59) + (2242049919433/500000000000 : ℝ)*(major_s1_0) + (2242049919433/500000000000 : ℝ)*(major_s1_1) + (2242049919433/500000000000 : ℝ)*(major_s1_2) + (14190499/1000000000000 : ℝ)*(sp_s1_0) + (1821913/1000000000000 : ℝ)*(sp_s1_2) + (40657453/1000000000000 : ℝ)*(sp_s1_9) + (6438461850837/1000000000000 : ℝ)*(sp_s1_21) + (643848141393/100000000000 : ℝ)*(sp_s1_22) + (3219219475981/500000000000 : ℝ)*(sp_s1_23) + (632429162017/250000000000 : ℝ)*(sp_s1_27) + (632429162017/250000000000 : ℝ)*(f.failure) + (6438481431327/1000000000000 : ℝ)*(f.sum) + (55044240546354045247/274545093800000000000000000000000 : ℝ)*base63 + (1496353949221603/3485800000000000000000000000 : ℝ)*base64 + (8825745027949/28956250000000000000000000 : ℝ)*base67 + (856323977648909/3485800000000000000000000000 : ℝ)*base68 + (2359845361714777883/137950535000000000000000000000000 : ℝ)*base70 + (336581449055291/494687500000000000000000000 : ℝ)*base73 + (317468944914043/492256250000000000000000000 : ℝ)*base74 + (3946803510922101/3957500000000000000000000000 : ℝ)*base76 + (793660070927278481/4583774375000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (2631/25000000000000000 : ℝ)*base86 + (2631/25000000000000000 : ℝ)*base88 + (2631/25000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (19/4 : ℝ) ≤ p) (hpb : p ≤ (77/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (177257/100000 : ℝ) (173433/100000 : ℝ) (1587/2000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, false]])
    (hprev0 : (0 : ℝ) ≤ ((1583/2000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1583/2000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(78761/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(78761/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-17429/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-17429/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((11829/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11829/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(52251/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(52251/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8959/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-8959/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c316060_s1 p hpa hpb X hX hprev0

#print axioms solution
