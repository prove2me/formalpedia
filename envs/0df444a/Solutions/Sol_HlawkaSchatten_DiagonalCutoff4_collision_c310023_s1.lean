-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c310023_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:23:20.109219+00:00
-- url     : https://prove2.me/submissions/623e77bd-e9fb-4b90-8402-0d2f56b131fd

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
theorem collision_support_c310023_s1_s1_2 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2955671411/10000000000 : ℝ)*x 0 + (1244077581/2000000000 : ℝ)*x 1 + (-3383079581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2955671411/10000000000 : ℝ)^9 ≤ (1043241981717/5000000000000 : ℝ)^7 := by
    have hnat : (2955671411 : ℕ)^9*5000000000000^7 ≤ 1043241981717^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2955671411 10000000000 1043241981717 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1244077581/2000000000 : ℝ)^9 ≤ (27156773982497/50000000000000 : ℝ)^7 := by
    have hnat : (1244077581 : ℕ)^9*50000000000000^7 ≤ 27156773982497^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1244077581 2000000000 27156773982497 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3383079581/10000000000 : ℝ)^9 ≤ (3102701547779/12500000000000 : ℝ)^7 := by
    have hnat : (3383079581 : ℕ)^9*12500000000000^7 ≤ 3102701547779^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3383079581 10000000000 3102701547779 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2955671411/10000000000 : ℝ), (1244077581/2000000000 : ℝ), (-3383079581/10000000000 : ℝ)] ![(1043241981717/5000000000000 : ℝ), (27156773982497/50000000000000 : ℝ), (3102701547779/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2955671411/10000000000 : ℝ)|^9 ≤ (1043241981717/5000000000000 : ℝ)^7
        have hw : |(2955671411/10000000000 : ℝ)|=(2955671411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1244077581/2000000000 : ℝ)|^9 ≤ (27156773982497/50000000000000 : ℝ)^7
        have hw : |(1244077581/2000000000 : ℝ)|=(1244077581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3383079581/10000000000 : ℝ)|^9 ≤ (3102701547779/12500000000000 : ℝ)^7
        have hw : |(-3383079581/10000000000 : ℝ)|=(3383079581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310023_s1_s1_6 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4185676779/10000000000 : ℝ)*x 0 + (2422507813/5000000000 : ℝ)*x 1 + (742563197/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4185676779/10000000000 : ℝ)^9 ≤ (16318068317819/50000000000000 : ℝ)^7 := by
    have hnat : (4185676779 : ℕ)^9*50000000000000^7 ≤ 16318068317819^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4185676779 10000000000 16318068317819 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2422507813/5000000000 : ℝ)^9 ≤ (39389413997943/100000000000000 : ℝ)^7 := by
    have hnat : (2422507813 : ℕ)^9*100000000000000^7 ≤ 39389413997943^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2422507813 5000000000 39389413997943 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (742563197/2000000000 : ℝ)^9 ≤ (5594889871013/20000000000000 : ℝ)^7 := by
    have hnat : (742563197 : ℕ)^9*20000000000000^7 ≤ 5594889871013^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      742563197 2000000000 5594889871013 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4185676779/10000000000 : ℝ), (2422507813/5000000000 : ℝ), (742563197/2000000000 : ℝ)] ![(16318068317819/50000000000000 : ℝ), (39389413997943/100000000000000 : ℝ), (5594889871013/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4185676779/10000000000 : ℝ)|^9 ≤ (16318068317819/50000000000000 : ℝ)^7
        have hw : |(4185676779/10000000000 : ℝ)|=(4185676779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2422507813/5000000000 : ℝ)|^9 ≤ (39389413997943/100000000000000 : ℝ)^7
        have hw : |(2422507813/5000000000 : ℝ)|=(2422507813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(742563197/2000000000 : ℝ)|^9 ≤ (5594889871013/20000000000000 : ℝ)^7
        have hw : |(742563197/2000000000 : ℝ)|=(742563197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310023_s1_s1_7 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-1678284821/5000000000 : ℝ)*x 0 + (4358798839/10000000000 : ℝ)*x 1 + (5002806357/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1678284821/5000000000 : ℝ)^9 ≤ (24571817448547/100000000000000 : ℝ)^7 := by
    have hnat : (1678284821 : ℕ)^9*100000000000000^7 ≤ 24571817448547^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1678284821 5000000000 24571817448547 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4358798839/10000000000 : ℝ)^9 ≤ (6876362648971/20000000000000 : ℝ)^7 := by
    have hnat : (4358798839 : ℕ)^9*20000000000000^7 ≤ 6876362648971^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358798839 10000000000 6876362648971 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5002806357/10000000000 : ℝ)^9 ≤ (2052318464727/5000000000000 : ℝ)^7 := by
    have hnat : (5002806357 : ℕ)^9*5000000000000^7 ≤ 2052318464727^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5002806357 10000000000 2052318464727 5000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1678284821/5000000000 : ℝ), (4358798839/10000000000 : ℝ), (5002806357/10000000000 : ℝ)] ![(24571817448547/100000000000000 : ℝ), (6876362648971/20000000000000 : ℝ), (2052318464727/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1678284821/5000000000 : ℝ)|^9 ≤ (24571817448547/100000000000000 : ℝ)^7
        have hw : |(-1678284821/5000000000 : ℝ)|=(1678284821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4358798839/10000000000 : ℝ)|^9 ≤ (6876362648971/20000000000000 : ℝ)^7
        have hw : |(4358798839/10000000000 : ℝ)|=(4358798839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5002806357/10000000000 : ℝ)|^9 ≤ (2052318464727/5000000000000 : ℝ)^7
        have hw : |(5002806357/10000000000 : ℝ)|=(5002806357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310023_s1_s1_8 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1086293031/2000000000 : ℝ)*x 0 + (3194263/1000000000 : ℝ)*x 1 + (1555143999/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1086293031/2000000000 : ℝ)^9 ≤ (22811245651037/50000000000000 : ℝ)^7 := by
    have hnat : (1086293031 : ℕ)^9*50000000000000^7 ≤ 22811245651037^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086293031 2000000000 22811245651037 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3194263/1000000000 : ℝ)^9 ≤ (61849147773/100000000000000 : ℝ)^7 := by
    have hnat : (3194263 : ℕ)^9*100000000000000^7 ≤ 61849147773^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3194263 1000000000 61849147773 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1555143999/2500000000 : ℝ)^9 ≤ (27157829766483/50000000000000 : ℝ)^7 := by
    have hnat : (1555143999 : ℕ)^9*50000000000000^7 ≤ 27157829766483^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1555143999 2500000000 27157829766483 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1086293031/2000000000 : ℝ), (3194263/1000000000 : ℝ), (1555143999/2500000000 : ℝ)] ![(22811245651037/50000000000000 : ℝ), (61849147773/100000000000000 : ℝ), (27157829766483/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1086293031/2000000000 : ℝ)|^9 ≤ (22811245651037/50000000000000 : ℝ)^7
        have hw : |(1086293031/2000000000 : ℝ)|=(1086293031/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3194263/1000000000 : ℝ)|^9 ≤ (61849147773/100000000000000 : ℝ)^7
        have hw : |(3194263/1000000000 : ℝ)|=(3194263/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1555143999/2500000000 : ℝ)|^9 ≤ (27157829766483/50000000000000 : ℝ)^7
        have hw : |(1555143999/2500000000 : ℝ)|=(1555143999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310023_s1_s1_9 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (26832071/156250000 : ℝ)*x 0 + (7768635357/10000000000 : ℝ)*x 1 + (-511896541/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (26832071/156250000 : ℝ)^9 ≤ (10380430364831/100000000000000 : ℝ)^7 := by
    have hnat : (26832071 : ℕ)^9*100000000000000^7 ≤ 10380430364831^7*156250000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26832071 156250000 10380430364831 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7768635357/10000000000 : ℝ)^9 ≤ (18069855125461/25000000000000 : ℝ)^7 := by
    have hnat : (7768635357 : ℕ)^9*25000000000000^7 ≤ 18069855125461^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7768635357 10000000000 18069855125461 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (511896541/2000000000 : ℝ)^9 ≤ (4335037276779/25000000000000 : ℝ)^7 := by
    have hnat : (511896541 : ℕ)^9*25000000000000^7 ≤ 4335037276779^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      511896541 2000000000 4335037276779 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(26832071/156250000 : ℝ), (7768635357/10000000000 : ℝ), (-511896541/2000000000 : ℝ)] ![(10380430364831/100000000000000 : ℝ), (18069855125461/25000000000000 : ℝ), (4335037276779/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(26832071/156250000 : ℝ)|^9 ≤ (10380430364831/100000000000000 : ℝ)^7
        have hw : |(26832071/156250000 : ℝ)|=(26832071/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7768635357/10000000000 : ℝ)|^9 ≤ (18069855125461/25000000000000 : ℝ)^7
        have hw : |(7768635357/10000000000 : ℝ)|=(7768635357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-511896541/2000000000 : ℝ)|^9 ≤ (4335037276779/25000000000000 : ℝ)^7
        have hw : |(-511896541/2000000000 : ℝ)|=(511896541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310023_s1_s1_12 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (3126050419/10000000000 : ℝ)*x 0 + (2956150613/5000000000 : ℝ)*x 1 + (35802189/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3126050419/10000000000 : ℝ)^9 ≤ (22423795029639/100000000000000 : ℝ)^7 := by
    have hnat : (3126050419 : ℕ)^9*100000000000000^7 ≤ 22423795029639^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3126050419 10000000000 22423795029639 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2956150613/5000000000 : ℝ)^9 ≤ (50879652835989/100000000000000 : ℝ)^7 := by
    have hnat : (2956150613 : ℕ)^9*100000000000000^7 ≤ 50879652835989^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2956150613 5000000000 50879652835989 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (35802189/100000000 : ℝ)^9 ≤ (26696552113233/100000000000000 : ℝ)^7 := by
    have hnat : (35802189 : ℕ)^9*100000000000000^7 ≤ 26696552113233^7*100000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35802189 100000000 26696552113233 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3126050419/10000000000 : ℝ), (2956150613/5000000000 : ℝ), (35802189/100000000 : ℝ)] ![(22423795029639/100000000000000 : ℝ), (50879652835989/100000000000000 : ℝ), (26696552113233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3126050419/10000000000 : ℝ)|^9 ≤ (22423795029639/100000000000000 : ℝ)^7
        have hw : |(3126050419/10000000000 : ℝ)|=(3126050419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2956150613/5000000000 : ℝ)|^9 ≤ (50879652835989/100000000000000 : ℝ)^7
        have hw : |(2956150613/5000000000 : ℝ)|=(2956150613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(35802189/100000000 : ℝ)|^9 ≤ (26696552113233/100000000000000 : ℝ)^7
        have hw : |(35802189/100000000 : ℝ)|=(35802189/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310023_s1_s1_13 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-2169470453/5000000000 : ℝ)*x 0 + (5054850573/10000000000 : ℝ)*x 1 + (3319477599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169470453/5000000000 : ℝ)^9 ≤ (34180553272551/100000000000000 : ℝ)^7 := by
    have hnat : (2169470453 : ℕ)^9*100000000000000^7 ≤ 34180553272551^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169470453 5000000000 34180553272551 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5054850573/10000000000 : ℝ)^9 ≤ (41596190329277/100000000000000 : ℝ)^7 := by
    have hnat : (5054850573 : ℕ)^9*100000000000000^7 ≤ 41596190329277^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5054850573 10000000000 41596190329277 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3319477599/10000000000 : ℝ)^9 ≤ (12111628187767/50000000000000 : ℝ)^7 := by
    have hnat : (3319477599 : ℕ)^9*50000000000000^7 ≤ 12111628187767^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3319477599 10000000000 12111628187767 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2169470453/5000000000 : ℝ), (5054850573/10000000000 : ℝ), (3319477599/10000000000 : ℝ)] ![(34180553272551/100000000000000 : ℝ), (41596190329277/100000000000000 : ℝ), (12111628187767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2169470453/5000000000 : ℝ)|^9 ≤ (34180553272551/100000000000000 : ℝ)^7
        have hw : |(-2169470453/5000000000 : ℝ)|=(2169470453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5054850573/10000000000 : ℝ)|^9 ≤ (41596190329277/100000000000000 : ℝ)^7
        have hw : |(5054850573/10000000000 : ℝ)|=(5054850573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3319477599/10000000000 : ℝ)|^9 ≤ (12111628187767/50000000000000 : ℝ)^7
        have hw : |(3319477599/10000000000 : ℝ)|=(3319477599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310023_s1_s1_14 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (83726303/125000000 : ℝ)*x 0 + (-6288857/2000000000 : ℝ)*x 1 + (4922871101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (83726303/125000000 : ℝ)^9 ≤ (59734313102953/100000000000000 : ℝ)^7 := by
    have hnat : (83726303 : ℕ)^9*100000000000000^7 ≤ 59734313102953^7*125000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      83726303 125000000 59734313102953 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6288857/2000000000 : ℝ)^9 ≤ (15152826609/25000000000000 : ℝ)^7 := by
    have hnat : (6288857 : ℕ)^9*25000000000000^7 ≤ 15152826609^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6288857 2000000000 15152826609 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4922871101/10000000000 : ℝ)^9 ≤ (10051268895941/25000000000000 : ℝ)^7 := by
    have hnat : (4922871101 : ℕ)^9*25000000000000^7 ≤ 10051268895941^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4922871101 10000000000 10051268895941 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(83726303/125000000 : ℝ), (-6288857/2000000000 : ℝ), (4922871101/10000000000 : ℝ)] ![(59734313102953/100000000000000 : ℝ), (15152826609/25000000000000 : ℝ), (10051268895941/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(83726303/125000000 : ℝ)|^9 ≤ (59734313102953/100000000000000 : ℝ)^7
        have hw : |(83726303/125000000 : ℝ)|=(83726303/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6288857/2000000000 : ℝ)|^9 ≤ (15152826609/25000000000000 : ℝ)^7
        have hw : |(-6288857/2000000000 : ℝ)|=(6288857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4922871101/10000000000 : ℝ)|^9 ≤ (10051268895941/25000000000000 : ℝ)^7
        have hw : |(4922871101/10000000000 : ℝ)|=(4922871101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310023_s1_s1_15 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2008595697/10000000000 : ℝ)*x 0 + (304078247/500000000 : ℝ)*x 1 + (-2187312447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2008595697/10000000000 : ℝ)^9 ≤ (12697521724167/100000000000000 : ℝ)^7 := by
    have hnat : (2008595697 : ℕ)^9*100000000000000^7 ≤ 12697521724167^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008595697 10000000000 12697521724167 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (304078247/500000000 : ℝ)^9 ≤ (52760080336809/100000000000000 : ℝ)^7 := by
    have hnat : (304078247 : ℕ)^9*100000000000000^7 ≤ 52760080336809^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      304078247 500000000 52760080336809 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2187312447/5000000000 : ℝ)^9 ≤ (17271198960831/50000000000000 : ℝ)^7 := by
    have hnat : (2187312447 : ℕ)^9*50000000000000^7 ≤ 17271198960831^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187312447 5000000000 17271198960831 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2008595697/10000000000 : ℝ), (304078247/500000000 : ℝ), (-2187312447/5000000000 : ℝ)] ![(12697521724167/100000000000000 : ℝ), (52760080336809/100000000000000 : ℝ), (17271198960831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2008595697/10000000000 : ℝ)|^9 ≤ (12697521724167/100000000000000 : ℝ)^7
        have hw : |(2008595697/10000000000 : ℝ)|=(2008595697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(304078247/500000000 : ℝ)|^9 ≤ (52760080336809/100000000000000 : ℝ)^7
        have hw : |(304078247/500000000 : ℝ)|=(304078247/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2187312447/5000000000 : ℝ)|^9 ≤ (17271198960831/50000000000000 : ℝ)^7
        have hw : |(-2187312447/5000000000 : ℝ)|=(2187312447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310023_s1_s1_19 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (638074647/2000000000 : ℝ)*x 0 + (2673586003/5000000000 : ℝ)*x 1 + (2074406697/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (638074647/2000000000 : ℝ)^9 ≤ (2301875973421/10000000000000 : ℝ)^7 := by
    have hnat : (638074647 : ℕ)^9*10000000000000^7 ≤ 2301875973421^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      638074647 2000000000 2301875973421 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2673586003/5000000000 : ℝ)^9 ≤ (44714187290929/100000000000000 : ℝ)^7 := by
    have hnat : (2673586003 : ℕ)^9*100000000000000^7 ≤ 44714187290929^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673586003 5000000000 44714187290929 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2074406697/5000000000 : ℝ)^9 ≤ (6453410592617/20000000000000 : ℝ)^7 := by
    have hnat : (2074406697 : ℕ)^9*20000000000000^7 ≤ 6453410592617^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074406697 5000000000 6453410592617 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(638074647/2000000000 : ℝ), (2673586003/5000000000 : ℝ), (2074406697/5000000000 : ℝ)] ![(2301875973421/10000000000000 : ℝ), (44714187290929/100000000000000 : ℝ), (6453410592617/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(638074647/2000000000 : ℝ)|^9 ≤ (2301875973421/10000000000000 : ℝ)^7
        have hw : |(638074647/2000000000 : ℝ)|=(638074647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2673586003/5000000000 : ℝ)|^9 ≤ (44714187290929/100000000000000 : ℝ)^7
        have hw : |(2673586003/5000000000 : ℝ)|=(2673586003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2074406697/5000000000 : ℝ)|^9 ≤ (6453410592617/20000000000000 : ℝ)^7
        have hw : |(2074406697/5000000000 : ℝ)|=(2074406697/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310023_s1_s1_20 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-600447221/2500000000 : ℝ)*x 0 + (6332175621/10000000000 : ℝ)*x 1 + (3761758781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (600447221/2500000000 : ℝ)^9 ≤ (1597882285371/10000000000000 : ℝ)^7 := by
    have hnat : (600447221 : ℕ)^9*10000000000000^7 ≤ 1597882285371^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600447221 2500000000 1597882285371 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6332175621/10000000000 : ℝ)^9 ≤ (55571714344037/100000000000000 : ℝ)^7 := by
    have hnat : (6332175621 : ℕ)^9*100000000000000^7 ≤ 55571714344037^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6332175621 10000000000 55571714344037 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3761758781/10000000000 : ℝ)^9 ≤ (1137978511743/4000000000000 : ℝ)^7 := by
    have hnat : (3761758781 : ℕ)^9*4000000000000^7 ≤ 1137978511743^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3761758781 10000000000 1137978511743 4000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-600447221/2500000000 : ℝ), (6332175621/10000000000 : ℝ), (3761758781/10000000000 : ℝ)] ![(1597882285371/10000000000000 : ℝ), (55571714344037/100000000000000 : ℝ), (1137978511743/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-600447221/2500000000 : ℝ)|^9 ≤ (1597882285371/10000000000000 : ℝ)^7
        have hw : |(-600447221/2500000000 : ℝ)|=(600447221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6332175621/10000000000 : ℝ)|^9 ≤ (55571714344037/100000000000000 : ℝ)^7
        have hw : |(6332175621/10000000000 : ℝ)|=(6332175621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3761758781/10000000000 : ℝ)|^9 ≤ (1137978511743/4000000000000 : ℝ)^7
        have hw : |(3761758781/10000000000 : ℝ)|=(3761758781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310023_s1_s1_21 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (7718020427/10000000000 : ℝ)*x 0 + (3615379/10000000000 : ℝ)*x 1 + (1874307893/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7718020427/10000000000 : ℝ)^9 ≤ (71674514358699/100000000000000 : ℝ)^7 := by
    have hnat : (7718020427 : ℕ)^9*100000000000000^7 ≤ 71674514358699^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7718020427 10000000000 71674514358699 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3615379/10000000000 : ℝ)^9 ≤ (751275467/20000000000000 : ℝ)^7 := by
    have hnat : (3615379 : ℕ)^9*20000000000000^7 ≤ 751275467^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3615379 10000000000 751275467 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1874307893/5000000000 : ℝ)^9 ≤ (14160864628201/50000000000000 : ℝ)^7 := by
    have hnat : (1874307893 : ℕ)^9*50000000000000^7 ≤ 14160864628201^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1874307893 5000000000 14160864628201 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7718020427/10000000000 : ℝ), (3615379/10000000000 : ℝ), (1874307893/5000000000 : ℝ)] ![(71674514358699/100000000000000 : ℝ), (751275467/20000000000000 : ℝ), (14160864628201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7718020427/10000000000 : ℝ)|^9 ≤ (71674514358699/100000000000000 : ℝ)^7
        have hw : |(7718020427/10000000000 : ℝ)|=(7718020427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3615379/10000000000 : ℝ)|^9 ≤ (751275467/20000000000000 : ℝ)^7
        have hw : |(3615379/10000000000 : ℝ)|=(3615379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1874307893/5000000000 : ℝ)|^9 ≤ (14160864628201/50000000000000 : ℝ)^7
        have hw : |(1874307893/5000000000 : ℝ)|=(1874307893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310023_s1_s1_22 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1867015973/10000000000 : ℝ)*x 0 + (7396780893/10000000000 : ℝ)*x 1 + (-2924180297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1867015973/10000000000 : ℝ)^9 ≤ (361205734203/3125000000000 : ℝ)^7 := by
    have hnat : (1867015973 : ℕ)^9*3125000000000^7 ≤ 361205734203^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1867015973 10000000000 361205734203 3125000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7396780893/10000000000 : ℝ)^9 ≤ (33930979958199/50000000000000 : ℝ)^7 := by
    have hnat : (7396780893 : ℕ)^9*50000000000000^7 ≤ 33930979958199^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7396780893 10000000000 33930979958199 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2924180297/10000000000 : ℝ)^9 ≤ (10289728291337/50000000000000 : ℝ)^7 := by
    have hnat : (2924180297 : ℕ)^9*50000000000000^7 ≤ 10289728291337^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2924180297 10000000000 10289728291337 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1867015973/10000000000 : ℝ), (7396780893/10000000000 : ℝ), (-2924180297/10000000000 : ℝ)] ![(361205734203/3125000000000 : ℝ), (33930979958199/50000000000000 : ℝ), (10289728291337/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1867015973/10000000000 : ℝ)|^9 ≤ (361205734203/3125000000000 : ℝ)^7
        have hw : |(1867015973/10000000000 : ℝ)|=(1867015973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7396780893/10000000000 : ℝ)|^9 ≤ (33930979958199/50000000000000 : ℝ)^7
        have hw : |(7396780893/10000000000 : ℝ)|=(7396780893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2924180297/10000000000 : ℝ)|^9 ≤ (10289728291337/50000000000000 : ℝ)^7
        have hw : |(-2924180297/10000000000 : ℝ)|=(2924180297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c310023_s1_s1_25 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (6048041713/10000000000 : ℝ)*x 0 + (3602814177/10000000000 : ℝ)*x 1 + (2937512909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6048041713/10000000000 : ℝ)^9 ≤ (5238645371839/10000000000000 : ℝ)^7 := by
    have hnat : (6048041713 : ℕ)^9*10000000000000^7 ≤ 5238645371839^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6048041713 10000000000 5238645371839 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3602814177/10000000000 : ℝ)^9 ≤ (1682085731723/6250000000000 : ℝ)^7 := by
    have hnat : (3602814177 : ℕ)^9*6250000000000^7 ≤ 1682085731723^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3602814177 10000000000 1682085731723 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2937512909/10000000000 : ℝ)^9 ≤ (41400349117/200000000000 : ℝ)^7 := by
    have hnat : (2937512909 : ℕ)^9*200000000000^7 ≤ 41400349117^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2937512909 10000000000 41400349117 200000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6048041713/10000000000 : ℝ), (3602814177/10000000000 : ℝ), (2937512909/10000000000 : ℝ)] ![(5238645371839/10000000000000 : ℝ), (1682085731723/6250000000000 : ℝ), (41400349117/200000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6048041713/10000000000 : ℝ)|^9 ≤ (5238645371839/10000000000000 : ℝ)^7
        have hw : |(6048041713/10000000000 : ℝ)|=(6048041713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3602814177/10000000000 : ℝ)|^9 ≤ (1682085731723/6250000000000 : ℝ)^7
        have hw : |(3602814177/10000000000 : ℝ)|=(3602814177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2937512909/10000000000 : ℝ)|^9 ≤ (41400349117/200000000000 : ℝ)^7
        have hw : |(2937512909/10000000000 : ℝ)|=(2937512909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c310023_s1 (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((79917/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(79917/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(49991/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(49991/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21941/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(21941/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((58423/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(58423/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(12529/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(12529/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6547/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6547/10000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (2431/3125 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (2431/3125 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (2431/3125 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (18111/10000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base50 : ((1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (79917/100000 : ℝ) ^ (35/8 : ℝ) ≤ (9375326229833665989/25000000000000000000 : ℝ) := by
    have hpowers : (79917/100000 : ℝ)^35 ≤ (9375326229833665989/25000000000000000000 : ℝ)^8 := by
      have hnat : (79917 : ℕ)^35*25000000000000000000^8 ≤ 9375326229833665989^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79917 100000 9375326229833665989 25000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (79917/100000 : ℝ)) (X := (9375326229833665989/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (34375326229833665989/25000000000000000000 : ℝ) ≤ (10755063709972397/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (34375326229833665989/25000000000000000000 : ℝ)^8 ≤ (10755063709972397/10000000000000000 : ℝ)^35 := by
      have hnat : (34375326229833665989 : ℕ)^8*10000000000000000^35 ≤ 10755063709972397^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34375326229833665989 25000000000000000000 10755063709972397 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10755063709972397/10000000000000000 : ℝ)) (X := (34375326229833665989/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (21875326229833665989/12500000000000000000 : ℝ) ≤ (2841142672480211/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (21875326229833665989/12500000000000000000 : ℝ)^8 ≤ (2841142672480211/2500000000000000 : ℝ)^35 := by
      have hnat : (21875326229833665989 : ℕ)^8*2500000000000000^35 ≤ 2841142672480211^35*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21875326229833665989 12500000000000000000 2841142672480211 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2841142672480211/2500000000000000 : ℝ)) (X := (21875326229833665989/12500000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(755063709972397/7991700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(203168993316149/2663900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (79917/100000 : ℝ)) (alpha := (755063709972397/7991700000000000 : ℝ)) (beta := (203168993316149/2663900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (79917/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(755063709972397/7991700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(203168993316149/2663900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (49991/100000 : ℝ) ^ (35/8 : ℝ) ≤ (2407807348800024507/50000000000000000000 : ℝ) := by
    have hpowers : (49991/100000 : ℝ)^35 ≤ (2407807348800024507/50000000000000000000 : ℝ)^8 := by
      have hnat : (49991 : ℕ)^35*50000000000000000000^8 ≤ 2407807348800024507^8*100000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        49991 100000 2407807348800024507 50000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (49991/100000 : ℝ)) (X := (2407807348800024507/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (52407807348800024507/50000000000000000000 : ℝ) ≤ (2527020734584573/2500000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (52407807348800024507/50000000000000000000 : ℝ)^8 ≤ (2527020734584573/2500000000000000 : ℝ)^35 := by
      have hnat : (52407807348800024507 : ℕ)^8*2500000000000000^35 ≤ 2527020734584573^35*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52407807348800024507 50000000000000000000 2527020734584573 2500000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2527020734584573/2500000000000000 : ℝ)) (X := (52407807348800024507/50000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (27407807348800024507/25000000000000000000 : ℝ) ≤ (10212400457695569/10000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (27407807348800024507/25000000000000000000 : ℝ)^8 ≤ (10212400457695569/10000000000000000 : ℝ)^35 := by
      have hnat : (27407807348800024507 : ℕ)^8*10000000000000000^35 ≤ 10212400457695569^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27407807348800024507 25000000000000000000 10212400457695569 10000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10212400457695569/10000000000000000 : ℝ)) (X := (27407807348800024507/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(27020734584573/1249775000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(104317519357277/4999100000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (49991/100000 : ℝ)) (alpha := (27020734584573/1249775000000000 : ℝ)) (beta := (104317519357277/4999100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (49991/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(27020734584573/1249775000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(104317519357277/4999100000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (21941/25000 : ℝ) ^ (35/8 : ℝ) ≤ (14123726433344876609/25000000000000000000 : ℝ) := by
    have hpowers : (21941/25000 : ℝ)^35 ≤ (14123726433344876609/25000000000000000000 : ℝ)^8 := by
      have hnat : (21941 : ℕ)^35*25000000000000000000^8 ≤ 14123726433344876609^8*25000^35 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21941 25000 14123726433344876609 25000000000000000000 35 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21941/25000 : ℝ)) (X := (14123726433344876609/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (39123726433344876609/25000000000000000000 : ℝ) ≤ (5538946801533387/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (39123726433344876609/25000000000000000000 : ℝ)^8 ≤ (5538946801533387/5000000000000000 : ℝ)^35 := by
      have hnat : (39123726433344876609 : ℕ)^8*5000000000000000^35 ≤ 5538946801533387^35*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39123726433344876609 25000000000000000000 5538946801533387 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5538946801533387/5000000000000000 : ℝ)) (X := (39123726433344876609/25000000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (26623726433344876609/12500000000000000000 : ℝ) ≤ (5943242500137407/5000000000000000 : ℝ) ^ (35/8 : ℝ) := by
    have hpowers : (26623726433344876609/12500000000000000000 : ℝ)^8 ≤ (5943242500137407/5000000000000000 : ℝ)^35 := by
      have hnat : (26623726433344876609 : ℕ)^8*5000000000000000^35 ≤ 5943242500137407^35*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26623726433344876609 12500000000000000000 5943242500137407 5000000000000000 8 35 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5943242500137407/5000000000000000 : ℝ)) (X := (26623726433344876609/12500000000000000000 : ℝ)) (by norm_num) 35 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(538946801533387/4388200000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(20214784930201/219410000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (35/8 : ℝ)) (rho := (21941/25000 : ℝ)) (alpha := (538946801533387/4388200000000000 : ℝ)) (beta := (20214784930201/219410000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (21941/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(538946801533387/4388200000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(20214784930201/219410000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_2 : ((2955671411/10000000000 : ℝ)*X 2 0+(1244077581/2000000000 : ℝ)*X 2 1+(-3383079581/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4185676779/10000000000 : ℝ)*X 0 0+(2422507813/5000000000 : ℝ)*X 0 1+(742563197/2000000000 : ℝ)*X 0 2+(4185676779/10000000000 : ℝ)*X 1 0+(2422507813/5000000000 : ℝ)*X 1 1+(742563197/2000000000 : ℝ)*X 1 2+(4185676779/10000000000 : ℝ)*X 2 0+(2422507813/5000000000 : ℝ)*X 2 1+(742563197/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1678284821/5000000000 : ℝ)*X 0 0+(4358798839/10000000000 : ℝ)*X 0 1+(5002806357/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((1086293031/2000000000 : ℝ)*X 1 0+(3194263/1000000000 : ℝ)*X 1 1+(1555143999/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((26832071/156250000 : ℝ)*X 2 0+(7768635357/10000000000 : ℝ)*X 2 1+(-511896541/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_12 : ((3126050419/10000000000 : ℝ)*X 0 0+(2956150613/5000000000 : ℝ)*X 0 1+(35802189/100000000 : ℝ)*X 0 2+(3126050419/10000000000 : ℝ)*X 1 0+(2956150613/5000000000 : ℝ)*X 1 1+(35802189/100000000 : ℝ)*X 1 2+(3126050419/10000000000 : ℝ)*X 2 0+(2956150613/5000000000 : ℝ)*X 2 1+(35802189/100000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s1_s1_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((-2169470453/5000000000 : ℝ)*X 0 0+(5054850573/10000000000 : ℝ)*X 0 1+(3319477599/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s1_s1_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((83726303/125000000 : ℝ)*X 1 0+(-6288857/2000000000 : ℝ)*X 1 1+(4922871101/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s1_s1_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2008595697/10000000000 : ℝ)*X 2 0+(304078247/500000000 : ℝ)*X 2 1+(-2187312447/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s1_s1_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((638074647/2000000000 : ℝ)*X 0 0+(2673586003/5000000000 : ℝ)*X 0 1+(2074406697/5000000000 : ℝ)*X 0 2+(638074647/2000000000 : ℝ)*X 1 0+(2673586003/5000000000 : ℝ)*X 1 1+(2074406697/5000000000 : ℝ)*X 1 2+(638074647/2000000000 : ℝ)*X 2 0+(2673586003/5000000000 : ℝ)*X 2 1+(2074406697/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s1_s1_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((-600447221/2500000000 : ℝ)*X 0 0+(6332175621/10000000000 : ℝ)*X 0 1+(3761758781/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s1_s1_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((7718020427/10000000000 : ℝ)*X 1 0+(3615379/10000000000 : ℝ)*X 1 1+(1874307893/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s1_s1_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((1867015973/10000000000 : ℝ)*X 2 0+(7396780893/10000000000 : ℝ)*X 2 1+(-2924180297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s1_s1_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_25 : ((6048041713/10000000000 : ℝ)*X 0 0+(3602814177/10000000000 : ℝ)*X 0 1+(2937512909/10000000000 : ℝ)*X 0 2+(6048041713/10000000000 : ℝ)*X 1 0+(3602814177/10000000000 : ℝ)*X 1 1+(2937512909/10000000000 : ℝ)*X 1 2+(6048041713/10000000000 : ℝ)*X 2 0+(3602814177/10000000000 : ℝ)*X 2 1+(2937512909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c310023_s1_s1_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((58423/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(58423/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (68135432440459956606272566419/4296919790192500000000000000000000 : ℝ) := by norm_num
    linear_combination (352443630961/500000000000 : ℝ)*(base7) + (858652220653/1000000000000 : ℝ)*(base49) + (721729934999/1000000000000 : ℝ)*(base50) + (98591724931/1000000000000 : ℝ)*(base60) + (2652593103021/1000000000000 : ℝ)*(major_s1_0) + (2652593103021/1000000000000 : ℝ)*(major_s1_1) + (2652593103021/1000000000000 : ℝ)*(major_s1_2) + (810022361101/250000000000 : ℝ)*(sp_s1_7) + (648028483241/200000000000 : ℝ)*(sp_s1_8) + (810010396973/250000000000 : ℝ)*(sp_s1_9) + (1172163921699/500000000000 : ℝ)*(sp_s1_12) + (57482731/1000000000000 : ℝ)*(sp_s1_19) + (52971801/1000000000000 : ℝ)*(sp_s1_20) + (100828313/1000000000000 : ℝ)*(sp_s1_22) + (819749032103/500000000000 : ℝ)*(f.failure) + (648028483241/200000000000 : ℝ)*(f.sum) + (38742068013777529533/219370506200000000000000000000000 : ℝ)*base63 + (13937050566683/21941000000000000000000000 : ℝ)*base64 + (3550888132651747/4999100000000000000000000000 : ℝ)*base66 + (1918330533737913/4388200000000000000000000000 : ℝ)*base68 + (1381336978647637643/3438154700000000000000000000000 : ℝ)*base70 + (79873893412443/156700000000000000000000000 : ℝ)*base72 + (140885552634793/1249775000000000000000000000 : ℝ)*base74 + (93633861635303/156700000000000000000000000 : ℝ)*base76 + (1890793503648615141/3916794850000000000000000000000 : ℝ)*base78 + (9321/50000000000000000 : ℝ)*base86 + (9321/50000000000000000 : ℝ)*base88 + (9321/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(12529/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(12529/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (28781410392237280334786888441/3948520888285000000000000000000000 : ℝ) := by norm_num
    linear_combination (1159851/500000000000 : ℝ)*(base7) + (11082718939/40000000000 : ℝ)*(base40) + (10483538641/20000000000 : ℝ)*(base49) + (1263393/500000000000 : ℝ)*(base60) + (992830066813/500000000000 : ℝ)*(major_s1_0) + (992830066813/500000000000 : ℝ)*(major_s1_1) + (992830066813/500000000000 : ℝ)*(major_s1_2) + (69595413/500000000000 : ℝ)*(sp_s1_6) + (1021899/500000000000 : ℝ)*(sp_s1_7) + (36980359/500000000000 : ℝ)*(sp_s1_8) + (2744030064811/1000000000000 : ℝ)*(sp_s1_13) + (2743958147891/1000000000000 : ℝ)*(sp_s1_14) + (274403210861/100000000000 : ℝ)*(sp_s1_15) + (613573728693/500000000000 : ℝ)*(sp_s1_19) + (122728432851/100000000000 : ℝ)*(f.failure) + (274403210861/100000000000 : ℝ)*(f.sum) + (94969592963879983/2964466300000000000000000000000 : ℝ)*base62 + (3049763576183/5930000000000000000000000 : ℝ)*base64 + (230462555087101/624887500000000000000000000 : ℝ)*base67 + (19201912447543/59300000000000000000000000 : ℝ)*base69 + (1087160996154472841/1184769525000000000000000000000 : ℝ)*base70 + (222207752647801/665975000000000000000000000 : ℝ)*base73 + (598239661654183/1249775000000000000000000000 : ℝ)*base74 + (4120319707570559/3995850000000000000000000000 : ℝ)*base76 + (29453360836315417299/33292756225000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (1843/10000000000000000 : ℝ)*base87 + (1843/10000000000000000 : ℝ)*base89 + (1843/10000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6547/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6547/10000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (152665350807211482306668491/13317102490000000000000000000000 : ℝ) := by norm_num
    linear_combination (722416825129/1000000000000 : ℝ)*(base7) + (3039959/500000000000 : ℝ)*(base11) + (45463729693/125000000000 : ℝ)*(base40) + (177565472143/250000000000 : ℝ)*(base49) + (313153596127/500000000000 : ℝ)*(base50) + (708256002307/250000000000 : ℝ)*(major_s1_0) + (708256002307/250000000000 : ℝ)*(major_s1_1) + (708256002307/250000000000 : ℝ)*(major_s1_2) + (80897803/1000000000000 : ℝ)*(sp_s1_2) + (244594149/1000000000000 : ℝ)*(sp_s1_9) + (1739448707923/500000000000 : ℝ)*(sp_s1_20) + (869725873941/250000000000 : ℝ)*(sp_s1_21) + (869644500953/250000000000 : ℝ)*(sp_s1_22) + (1236717244599/500000000000 : ℝ)*(sp_s1_25) + (1751017664069/1000000000000 : ℝ)*(f.failure) + (869725873941/250000000000 : ℝ)*(f.sum) + (10164310890162445339/54842626550000000000000000000000 : ℝ)*base62 + (2242980362821/13713125000000000000000000 : ℝ)*base65 + (782957857027891/1249775000000000000000000000 : ℝ)*base67 + (219537102087399/1097050000000000000000000000 : ℝ)*base69 + (429588156370743541/2739779526562500000000000000000 : ℝ)*base70 + (166179874628429/332987500000000000000000000 : ℝ)*base73 + (332721504514033/2499550000000000000000000000 : ℝ)*base74 + (22018881205387/249740625000000000000000000 : ℝ)*base76 + (29440922301115586717/33292756225000000000000000000000 : ℝ)*base79 + (84283/100000000000000000 : ℝ)*base86 + (84283/100000000000000000 : ℝ)*base88 + (84283/100000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (35/8 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (161793/100000 : ℝ) (18111/10000 : ℝ) (2431/3125 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((79917/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(79917/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(49991/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(49991/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21941/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(21941/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((58423/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(58423/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(12529/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(12529/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(6547/10000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(6547/10000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c310023_s1 p hpa hpb X hX hprev0

#print axioms solution
