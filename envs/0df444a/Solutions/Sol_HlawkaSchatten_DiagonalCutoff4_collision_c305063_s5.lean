-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c305063_s5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:32:50.350626+00:00
-- url     : https://prove2.me/submissions/f5c94b04-dc78-4f76-a40a-7a9a414b7495

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
theorem collision_support_c305063_s5_s5_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-252383217/2000000000 : ℝ)*x 0 + (1387968147/2500000000 : ℝ)*x 1 + (2825634321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (252383217/2000000000 : ℝ)^67 ≤ (6591751422229/100000000000000 : ℝ)^51 := by
    have hnat : (252383217 : ℕ)^67*100000000000000^51 ≤ 6591751422229^51*2000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252383217 2000000000 6591751422229 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1387968147/2500000000 : ℝ)^67 ≤ (46159770908391/100000000000000 : ℝ)^51 := by
    have hnat : (1387968147 : ℕ)^67*100000000000000^51 ≤ 46159770908391^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1387968147 2500000000 46159770908391 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2825634321/5000000000 : ℝ)^67 ≤ (47248477661039/100000000000000 : ℝ)^51 := by
    have hnat : (2825634321 : ℕ)^67*100000000000000^51 ≤ 47248477661039^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2825634321 5000000000 47248477661039 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-252383217/2000000000 : ℝ), (1387968147/2500000000 : ℝ), (2825634321/5000000000 : ℝ)] ![(6591751422229/100000000000000 : ℝ), (46159770908391/100000000000000 : ℝ), (47248477661039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-252383217/2000000000 : ℝ)|^67 ≤ (6591751422229/100000000000000 : ℝ)^51
        have hw : |(-252383217/2000000000 : ℝ)|=(252383217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1387968147/2500000000 : ℝ)|^67 ≤ (46159770908391/100000000000000 : ℝ)^51
        have hw : |(1387968147/2500000000 : ℝ)|=(1387968147/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2825634321/5000000000 : ℝ)|^67 ≤ (47248477661039/100000000000000 : ℝ)^51
        have hw : |(2825634321/5000000000 : ℝ)|=(2825634321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s5_s5_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5553121401/10000000000 : ℝ)*x 0 + (-1277437099/10000000000 : ℝ)*x 1 + (2820153737/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5553121401/10000000000 : ℝ)^67 ≤ (11543352940233/25000000000000 : ℝ)^51 := by
    have hnat : (5553121401 : ℕ)^67*25000000000000^51 ≤ 11543352940233^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5553121401 10000000000 11543352940233 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1277437099/10000000000 : ℝ)^67 ≤ (3349233745413/50000000000000 : ℝ)^51 := by
    have hnat : (1277437099 : ℕ)^67*50000000000000^51 ≤ 3349233745413^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1277437099 10000000000 3349233745413 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2820153737/5000000000 : ℝ)^67 ≤ (5891015090899/12500000000000 : ℝ)^51 := by
    have hnat : (2820153737 : ℕ)^67*12500000000000^51 ≤ 5891015090899^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2820153737 5000000000 5891015090899 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5553121401/10000000000 : ℝ), (-1277437099/10000000000 : ℝ), (2820153737/5000000000 : ℝ)] ![(11543352940233/25000000000000 : ℝ), (3349233745413/50000000000000 : ℝ), (5891015090899/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5553121401/10000000000 : ℝ)|^67 ≤ (11543352940233/25000000000000 : ℝ)^51
        have hw : |(5553121401/10000000000 : ℝ)|=(5553121401/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1277437099/10000000000 : ℝ)|^67 ≤ (3349233745413/50000000000000 : ℝ)^51
        have hw : |(-1277437099/10000000000 : ℝ)|=(1277437099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2820153737/5000000000 : ℝ)|^67 ≤ (5891015090899/12500000000000 : ℝ)^51
        have hw : |(2820153737/5000000000 : ℝ)|=(2820153737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s5_s5_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5602495189/10000000000 : ℝ)*x 0 + (5624740969/10000000000 : ℝ)*x 1 + (-122346921/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5602495189/10000000000 : ℝ)^67 ≤ (46713494046449/100000000000000 : ℝ)^51 := by
    have hnat : (5602495189 : ℕ)^67*100000000000000^51 ≤ 46713494046449^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5602495189 10000000000 46713494046449 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5624740969/10000000000 : ℝ)^67 ≤ (9391464377963/20000000000000 : ℝ)^51 := by
    have hnat : (5624740969 : ℕ)^67*20000000000000^51 ≤ 9391464377963^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5624740969 10000000000 9391464377963 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (122346921/1000000000 : ℝ)^67 ≤ (3164592024401/50000000000000 : ℝ)^51 := by
    have hnat : (122346921 : ℕ)^67*50000000000000^51 ≤ 3164592024401^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      122346921 1000000000 3164592024401 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5602495189/10000000000 : ℝ), (5624740969/10000000000 : ℝ), (-122346921/1000000000 : ℝ)] ![(46713494046449/100000000000000 : ℝ), (9391464377963/20000000000000 : ℝ), (3164592024401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5602495189/10000000000 : ℝ)|^67 ≤ (46713494046449/100000000000000 : ℝ)^51
        have hw : |(5602495189/10000000000 : ℝ)|=(5602495189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5624740969/10000000000 : ℝ)|^67 ≤ (9391464377963/20000000000000 : ℝ)^51
        have hw : |(5624740969/10000000000 : ℝ)|=(5624740969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-122346921/1000000000 : ℝ)|^67 ≤ (3164592024401/50000000000000 : ℝ)^51
        have hw : |(-122346921/1000000000 : ℝ)|=(122346921/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s5_s5_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4427154819/10000000000 : ℝ)*x 0 + (4350213457/10000000000 : ℝ)*x 1 + (2110866311/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4427154819/10000000000 : ℝ)^67 ≤ (34285067649471/100000000000000 : ℝ)^51 := by
    have hnat : (4427154819 : ℕ)^67*100000000000000^51 ≤ 34285067649471^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4427154819 10000000000 34285067649471 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4350213457/10000000000 : ℝ)^67 ≤ (16752210536281/50000000000000 : ℝ)^51 := by
    have hnat : (4350213457 : ℕ)^67*50000000000000^51 ≤ 16752210536281^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350213457 10000000000 16752210536281 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2110866311/5000000000 : ℝ)^67 ≤ (3221051126611/10000000000000 : ℝ)^51 := by
    have hnat : (2110866311 : ℕ)^67*10000000000000^51 ≤ 3221051126611^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2110866311 5000000000 3221051126611 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4427154819/10000000000 : ℝ), (4350213457/10000000000 : ℝ), (2110866311/5000000000 : ℝ)] ![(34285067649471/100000000000000 : ℝ), (16752210536281/50000000000000 : ℝ), (3221051126611/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4427154819/10000000000 : ℝ)|^67 ≤ (34285067649471/100000000000000 : ℝ)^51
        have hw : |(4427154819/10000000000 : ℝ)|=(4427154819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4350213457/10000000000 : ℝ)|^67 ≤ (16752210536281/50000000000000 : ℝ)^51
        have hw : |(4350213457/10000000000 : ℝ)|=(4350213457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2110866311/5000000000 : ℝ)|^67 ≤ (3221051126611/10000000000000 : ℝ)^51
        have hw : |(2110866311/5000000000 : ℝ)|=(2110866311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s5_s5_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-968037909/10000000000 : ℝ)*x 0 + (1117271677/2500000000 : ℝ)*x 1 + (3416474603/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (968037909/10000000000 : ℝ)^67 ≤ (1163271153321/25000000000000 : ℝ)^51 := by
    have hnat : (968037909 : ℕ)^67*25000000000000^51 ≤ 1163271153321^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      968037909 10000000000 1163271153321 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1117271677/2500000000 : ℝ)^67 ≤ (17356154229691/50000000000000 : ℝ)^51 := by
    have hnat : (1117271677 : ℕ)^67*50000000000000^51 ≤ 17356154229691^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1117271677 2500000000 17356154229691 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3416474603/5000000000 : ℝ)^67 ≤ (6063460690651/10000000000000 : ℝ)^51 := by
    have hnat : (3416474603 : ℕ)^67*10000000000000^51 ≤ 6063460690651^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3416474603 5000000000 6063460690651 10000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-968037909/10000000000 : ℝ), (1117271677/2500000000 : ℝ), (3416474603/5000000000 : ℝ)] ![(1163271153321/25000000000000 : ℝ), (17356154229691/50000000000000 : ℝ), (6063460690651/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-968037909/10000000000 : ℝ)|^67 ≤ (1163271153321/25000000000000 : ℝ)^51
        have hw : |(-968037909/10000000000 : ℝ)|=(968037909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1117271677/2500000000 : ℝ)|^67 ≤ (17356154229691/50000000000000 : ℝ)^51
        have hw : |(1117271677/2500000000 : ℝ)|=(1117271677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3416474603/5000000000 : ℝ)|^67 ≤ (6063460690651/10000000000000 : ℝ)^51
        have hw : |(3416474603/5000000000 : ℝ)|=(3416474603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s5_s5_8 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4839085987/10000000000 : ℝ)*x 0 + (-291199691/10000000000 : ℝ)*x 1 + (3410866321/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4839085987/10000000000 : ℝ)^67 ≤ (9633976265203/25000000000000 : ℝ)^51 := by
    have hnat : (4839085987 : ℕ)^67*25000000000000^51 ≤ 9633976265203^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4839085987 10000000000 9633976265203 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (291199691/10000000000 : ℝ)^67 ≤ (19204298413/2000000000000 : ℝ)^51 := by
    have hnat : (291199691 : ℕ)^67*2000000000000^51 ≤ 19204298413^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      291199691 10000000000 19204298413 2000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3410866321/5000000000 : ℝ)^67 ≤ (60503880009231/100000000000000 : ℝ)^51 := by
    have hnat : (3410866321 : ℕ)^67*100000000000000^51 ≤ 60503880009231^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3410866321 5000000000 60503880009231 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4839085987/10000000000 : ℝ), (-291199691/10000000000 : ℝ), (3410866321/5000000000 : ℝ)] ![(9633976265203/25000000000000 : ℝ), (19204298413/2000000000000 : ℝ), (60503880009231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4839085987/10000000000 : ℝ)|^67 ≤ (9633976265203/25000000000000 : ℝ)^51
        have hw : |(4839085987/10000000000 : ℝ)|=(4839085987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-291199691/10000000000 : ℝ)|^67 ≤ (19204298413/2000000000000 : ℝ)^51
        have hw : |(-291199691/10000000000 : ℝ)|=(291199691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3410866321/5000000000 : ℝ)|^67 ≤ (60503880009231/100000000000000 : ℝ)^51
        have hw : |(3410866321/5000000000 : ℝ)|=(3410866321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s5_s5_9 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4574914851/10000000000 : ℝ)*x 0 + (3543331531/5000000000 : ℝ)*x 1 + (-8085369/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4574914851/10000000000 : ℝ)^67 ≤ (8949041436731/25000000000000 : ℝ)^51 := by
    have hnat : (4574914851 : ℕ)^67*25000000000000^51 ≤ 8949041436731^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4574914851 10000000000 8949041436731 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3543331531/5000000000 : ℝ)^67 ≤ (7951179778947/12500000000000 : ℝ)^51 := by
    have hnat : (3543331531 : ℕ)^67*12500000000000^51 ≤ 7951179778947^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3543331531 5000000000 7951179778947 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8085369/400000000 : ℝ)^67 ≤ (148599002757/25000000000000 : ℝ)^51 := by
    have hnat : (8085369 : ℕ)^67*25000000000000^51 ≤ 148599002757^51*400000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8085369 400000000 148599002757 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4574914851/10000000000 : ℝ), (3543331531/5000000000 : ℝ), (-8085369/400000000 : ℝ)] ![(8949041436731/25000000000000 : ℝ), (7951179778947/12500000000000 : ℝ), (148599002757/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4574914851/10000000000 : ℝ)|^67 ≤ (8949041436731/25000000000000 : ℝ)^51
        have hw : |(4574914851/10000000000 : ℝ)|=(4574914851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3543331531/5000000000 : ℝ)|^67 ≤ (7951179778947/12500000000000 : ℝ)^51
        have hw : |(3543331531/5000000000 : ℝ)|=(3543331531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8085369/400000000 : ℝ)|^67 ≤ (148599002757/25000000000000 : ℝ)^51
        have hw : |(-8085369/400000000 : ℝ)|=(8085369/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s5_s5_13 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (275588751/625000000 : ℝ)*x 0 + (6197944361/10000000000 : ℝ)*x 1 + (1030255107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (275588751/625000000 : ℝ)^67 ≤ (34104750074333/100000000000000 : ℝ)^51 := by
    have hnat : (275588751 : ℕ)^67*100000000000000^51 ≤ 34104750074333^51*625000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      275588751 625000000 34104750074333 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6197944361/10000000000 : ℝ)^67 ≤ (53342144644707/100000000000000 : ℝ)^51 := by
    have hnat : (6197944361 : ℕ)^67*100000000000000^51 ≤ 53342144644707^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6197944361 10000000000 53342144644707 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030255107/5000000000 : ℝ)^67 ≤ (12553105264487/100000000000000 : ℝ)^51 := by
    have hnat : (1030255107 : ℕ)^67*100000000000000^51 ≤ 12553105264487^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030255107 5000000000 12553105264487 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(275588751/625000000 : ℝ), (6197944361/10000000000 : ℝ), (1030255107/5000000000 : ℝ)] ![(34104750074333/100000000000000 : ℝ), (53342144644707/100000000000000 : ℝ), (12553105264487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(275588751/625000000 : ℝ)|^67 ≤ (34104750074333/100000000000000 : ℝ)^51
        have hw : |(275588751/625000000 : ℝ)|=(275588751/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6197944361/10000000000 : ℝ)|^67 ≤ (53342144644707/100000000000000 : ℝ)^51
        have hw : |(6197944361/10000000000 : ℝ)|=(6197944361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1030255107/5000000000 : ℝ)|^67 ≤ (12553105264487/100000000000000 : ℝ)^51
        have hw : |(1030255107/5000000000 : ℝ)|=(1030255107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s5_s5_14 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-258735203/10000000000 : ℝ)*x 0 + (4856011731/10000000000 : ℝ)*x 1 + (681837993/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258735203/10000000000 : ℝ)^67 ≤ (205526511721/25000000000000 : ℝ)^51 := by
    have hnat : (258735203 : ℕ)^67*25000000000000^51 ≤ 205526511721^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258735203 10000000000 205526511721 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4856011731/10000000000 : ℝ)^67 ≤ (387130760637/1000000000000 : ℝ)^51 := by
    have hnat : (4856011731 : ℕ)^67*1000000000000^51 ≤ 387130760637^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4856011731 10000000000 387130760637 1000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (681837993/1000000000 : ℝ)^67 ≤ (30232408939641/50000000000000 : ℝ)^51 := by
    have hnat : (681837993 : ℕ)^67*50000000000000^51 ≤ 30232408939641^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      681837993 1000000000 30232408939641 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-258735203/10000000000 : ℝ), (4856011731/10000000000 : ℝ), (681837993/1000000000 : ℝ)] ![(205526511721/25000000000000 : ℝ), (387130760637/1000000000000 : ℝ), (30232408939641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-258735203/10000000000 : ℝ)|^67 ≤ (205526511721/25000000000000 : ℝ)^51
        have hw : |(-258735203/10000000000 : ℝ)|=(258735203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4856011731/10000000000 : ℝ)|^67 ≤ (387130760637/1000000000000 : ℝ)^51
        have hw : |(4856011731/10000000000 : ℝ)|=(4856011731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(681837993/1000000000 : ℝ)|^67 ≤ (30232408939641/50000000000000 : ℝ)^51
        have hw : |(681837993/1000000000 : ℝ)|=(681837993/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s5_s5_15 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4506073081/10000000000 : ℝ)*x 0 + (-19114899/200000000 : ℝ)*x 1 + (6807163597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4506073081/10000000000 : ℝ)^67 ≤ (8772551368699/25000000000000 : ℝ)^51 := by
    have hnat : (4506073081 : ℕ)^67*25000000000000^51 ≤ 8772551368699^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4506073081 10000000000 8772551368699 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (19114899/200000000 : ℝ)^67 ≤ (915122651849/20000000000000 : ℝ)^51 := by
    have hnat : (19114899 : ℕ)^67*20000000000000^51 ≤ 915122651849^51*200000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19114899 200000000 915122651849 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6807163597/10000000000 : ℝ)^67 ≤ (60334181254697/100000000000000 : ℝ)^51 := by
    have hnat : (6807163597 : ℕ)^67*100000000000000^51 ≤ 60334181254697^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6807163597 10000000000 60334181254697 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4506073081/10000000000 : ℝ), (-19114899/200000000 : ℝ), (6807163597/10000000000 : ℝ)] ![(8772551368699/25000000000000 : ℝ), (915122651849/20000000000000 : ℝ), (60334181254697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4506073081/10000000000 : ℝ)|^67 ≤ (8772551368699/25000000000000 : ℝ)^51
        have hw : |(4506073081/10000000000 : ℝ)|=(4506073081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-19114899/200000000 : ℝ)|^67 ≤ (915122651849/20000000000000 : ℝ)^51
        have hw : |(-19114899/200000000 : ℝ)|=(19114899/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6807163597/10000000000 : ℝ)|^67 ≤ (60334181254697/100000000000000 : ℝ)^51
        have hw : |(6807163597/10000000000 : ℝ)|=(6807163597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s5_s5_16 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1691444757/2500000000 : ℝ)*x 0 + (4930581199/10000000000 : ℝ)*x 1 + (-27087853/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1691444757/2500000000 : ℝ)^67 ≤ (1496318997373/2500000000000 : ℝ)^51 := by
    have hnat : (1691444757 : ℕ)^67*2500000000000^51 ≤ 1496318997373^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1691444757 2500000000 1496318997373 2500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4930581199/10000000000 : ℝ)^67 ≤ (39495937416533/100000000000000 : ℝ)^51 := by
    have hnat : (4930581199 : ℕ)^67*100000000000000^51 ≤ 39495937416533^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4930581199 10000000000 39495937416533 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (27087853/1250000000 : ℝ)^67 ≤ (651302683719/100000000000000 : ℝ)^51 := by
    have hnat : (27087853 : ℕ)^67*100000000000000^51 ≤ 651302683719^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27087853 1250000000 651302683719 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1691444757/2500000000 : ℝ), (4930581199/10000000000 : ℝ), (-27087853/1250000000 : ℝ)] ![(1496318997373/2500000000000 : ℝ), (39495937416533/100000000000000 : ℝ), (651302683719/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1691444757/2500000000 : ℝ)|^67 ≤ (1496318997373/2500000000000 : ℝ)^51
        have hw : |(1691444757/2500000000 : ℝ)|=(1691444757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4930581199/10000000000 : ℝ)|^67 ≤ (39495937416533/100000000000000 : ℝ)^51
        have hw : |(4930581199/10000000000 : ℝ)|=(4930581199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-27087853/1250000000 : ℝ)|^67 ≤ (651302683719/100000000000000 : ℝ)^51
        have hw : |(-27087853/1250000000 : ℝ)|=(27087853/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s5_s5_20 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3424596443/5000000000 : ℝ)*x 0 + (1813326921/5000000000 : ℝ)*x 1 + (52262577/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3424596443/5000000000 : ℝ)^67 ≤ (60824043230489/100000000000000 : ℝ)^51 := by
    have hnat : (3424596443 : ℕ)^67*100000000000000^51 ≤ 60824043230489^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3424596443 5000000000 60824043230489 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1813326921/5000000000 : ℝ)^67 ≤ (26382256699259/100000000000000 : ℝ)^51 := by
    have hnat : (1813326921 : ℕ)^67*100000000000000^51 ≤ 26382256699259^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1813326921 5000000000 26382256699259 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52262577/250000000 : ℝ)^67 ≤ (639685002561/5000000000000 : ℝ)^51 := by
    have hnat : (52262577 : ℕ)^67*5000000000000^51 ≤ 639685002561^51*250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52262577 250000000 639685002561 5000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3424596443/5000000000 : ℝ), (1813326921/5000000000 : ℝ), (52262577/250000000 : ℝ)] ![(60824043230489/100000000000000 : ℝ), (26382256699259/100000000000000 : ℝ), (639685002561/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3424596443/5000000000 : ℝ)|^67 ≤ (60824043230489/100000000000000 : ℝ)^51
        have hw : |(3424596443/5000000000 : ℝ)|=(3424596443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1813326921/5000000000 : ℝ)|^67 ≤ (26382256699259/100000000000000 : ℝ)^51
        have hw : |(1813326921/5000000000 : ℝ)|=(1813326921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52262577/250000000 : ℝ)|^67 ≤ (639685002561/5000000000000 : ℝ)^51
        have hw : |(52262577/250000000 : ℝ)|=(52262577/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s5_s5_21 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-10443267/500000000 : ℝ)*x 0 + (1593221093/2500000000 : ℝ)*x 1 + (5357704257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10443267/500000000 : ℝ)^67 ≤ (124106814509/20000000000000 : ℝ)^51 := by
    have hnat : (10443267 : ℕ)^67*20000000000000^51 ≤ 124106814509^51*500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10443267 500000000 124106814509 20000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1593221093/2500000000 : ℝ)^67 ≤ (13832200496157/25000000000000 : ℝ)^51 := by
    have hnat : (1593221093 : ℕ)^67*25000000000000^51 ≤ 13832200496157^51*2500000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1593221093 2500000000 13832200496157 25000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5357704257/10000000000 : ℝ)^67 ≤ (44050663932669/100000000000000 : ℝ)^51 := by
    have hnat : (5357704257 : ℕ)^67*100000000000000^51 ≤ 44050663932669^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5357704257 10000000000 44050663932669 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-10443267/500000000 : ℝ), (1593221093/2500000000 : ℝ), (5357704257/10000000000 : ℝ)] ![(124106814509/20000000000000 : ℝ), (13832200496157/25000000000000 : ℝ), (44050663932669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-10443267/500000000 : ℝ)|^67 ≤ (124106814509/20000000000000 : ℝ)^51
        have hw : |(-10443267/500000000 : ℝ)|=(10443267/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1593221093/2500000000 : ℝ)|^67 ≤ (13832200496157/25000000000000 : ℝ)^51
        have hw : |(1593221093/2500000000 : ℝ)|=(1593221093/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5357704257/10000000000 : ℝ)|^67 ≤ (44050663932669/100000000000000 : ℝ)^51
        have hw : |(5357704257/10000000000 : ℝ)|=(5357704257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s5_s5_22 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6765125703/10000000000 : ℝ)*x 0 + (-102456497/5000000000 : ℝ)*x 1 + (493568719/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6765125703/10000000000 : ℝ)^67 ≤ (59845167239391/100000000000000 : ℝ)^51 := by
    have hnat : (6765125703 : ℕ)^67*100000000000000^51 ≤ 59845167239391^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6765125703 10000000000 59845167239391 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (102456497/5000000000 : ℝ)^67 ≤ (605153866203/100000000000000 : ℝ)^51 := by
    have hnat : (102456497 : ℕ)^67*100000000000000^51 ≤ 605153866203^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102456497 5000000000 605153866203 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (493568719/1000000000 : ℝ)^67 ≤ (39549678882383/100000000000000 : ℝ)^51 := by
    have hnat : (493568719 : ℕ)^67*100000000000000^51 ≤ 39549678882383^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493568719 1000000000 39549678882383 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6765125703/10000000000 : ℝ), (-102456497/5000000000 : ℝ), (493568719/1000000000 : ℝ)] ![(59845167239391/100000000000000 : ℝ), (605153866203/100000000000000 : ℝ), (39549678882383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6765125703/10000000000 : ℝ)|^67 ≤ (59845167239391/100000000000000 : ℝ)^51
        have hw : |(6765125703/10000000000 : ℝ)|=(6765125703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-102456497/5000000000 : ℝ)|^67 ≤ (605153866203/100000000000000 : ℝ)^51
        have hw : |(-102456497/5000000000 : ℝ)|=(102456497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(493568719/1000000000 : ℝ)|^67 ≤ (39549678882383/100000000000000 : ℝ)^51
        have hw : |(493568719/1000000000 : ℝ)|=(493568719/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s5_s5_23 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (560258453/1250000000 : ℝ)*x 0 + (3429127139/5000000000 : ℝ)*x 1 + (-899535603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (560258453/1250000000 : ℝ)^67 ≤ (34844825698851/100000000000000 : ℝ)^51 := by
    have hnat : (560258453 : ℕ)^67*100000000000000^51 ≤ 34844825698851^51*1250000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560258453 1250000000 34844825698851 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3429127139/5000000000 : ℝ)^67 ≤ (30464889937693/50000000000000 : ℝ)^51 := by
    have hnat : (3429127139 : ℕ)^67*50000000000000^51 ≤ 30464889937693^51*5000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3429127139 5000000000 30464889937693 50000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (899535603/10000000000 : ℝ)^67 ≤ (528174301271/12500000000000 : ℝ)^51 := by
    have hnat : (899535603 : ℕ)^67*12500000000000^51 ≤ 528174301271^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      899535603 10000000000 528174301271 12500000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(560258453/1250000000 : ℝ), (3429127139/5000000000 : ℝ), (-899535603/10000000000 : ℝ)] ![(34844825698851/100000000000000 : ℝ), (30464889937693/50000000000000 : ℝ), (528174301271/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(560258453/1250000000 : ℝ)|^67 ≤ (34844825698851/100000000000000 : ℝ)^51
        have hw : |(560258453/1250000000 : ℝ)|=(560258453/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3429127139/5000000000 : ℝ)|^67 ≤ (30464889937693/50000000000000 : ℝ)^51
        have hw : |(3429127139/5000000000 : ℝ)|=(3429127139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-899535603/10000000000 : ℝ)|^67 ≤ (528174301271/12500000000000 : ℝ)^51
        have hw : |(-899535603/10000000000 : ℝ)|=(899535603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c305063_s5_s5_27 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7002618327/10000000000 : ℝ)*x 0 + (2926679161/10000000000 : ℝ)*x 1 + (265049463/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7002618327/10000000000 : ℝ)^67 ≤ (62620238416521/100000000000000 : ℝ)^51 := by
    have hnat : (7002618327 : ℕ)^67*100000000000000^51 ≤ 62620238416521^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7002618327 10000000000 62620238416521 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2926679161/10000000000 : ℝ)^67 ≤ (1244065951149/6250000000000 : ℝ)^51 := by
    have hnat : (2926679161 : ℕ)^67*6250000000000^51 ≤ 1244065951149^51*10000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2926679161 10000000000 1244065951149 6250000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (265049463/1000000000 : ℝ)^67 ≤ (17474706358463/100000000000000 : ℝ)^51 := by
    have hnat : (265049463 : ℕ)^67*100000000000000^51 ≤ 17474706358463^51*1000000000^67 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265049463 1000000000 17474706358463 100000000000000 67 51 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (67/16 : ℝ)) 67 51 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7002618327/10000000000 : ℝ), (2926679161/10000000000 : ℝ), (265049463/1000000000 : ℝ)] ![(62620238416521/100000000000000 : ℝ), (1244065951149/6250000000000 : ℝ), (17474706358463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7002618327/10000000000 : ℝ)|^67 ≤ (62620238416521/100000000000000 : ℝ)^51
        have hw : |(7002618327/10000000000 : ℝ)|=(7002618327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2926679161/10000000000 : ℝ)|^67 ≤ (1244065951149/6250000000000 : ℝ)^51
        have hw : |(2926679161/10000000000 : ℝ)|=(2926679161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(265049463/1000000000 : ℝ)|^67 ≤ (17474706358463/100000000000000 : ℝ)^51
        have hw : |(265049463/1000000000 : ℝ)|=(265049463/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c305063_s5 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev4 : (0 : ℝ) ≤ ((16351/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16351/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(66141/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(66141/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15883/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15883/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((26183/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26183/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(53271/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(53271/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(50937/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(50937/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (76771/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (76771/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (76771/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev4 with ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩
  have s5_pow0 : (16351/25000 : ℝ) ^ (133/32 : ℝ) ≤ (4281001909537479419/25000000000000000000 : ℝ) := by
    have hpowers : (16351/25000 : ℝ)^133 ≤ (4281001909537479419/25000000000000000000 : ℝ)^32 := by
      have hnat : (16351 : ℕ)^133*25000000000000000000^32 ≤ 4281001909537479419^32*25000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16351 25000 4281001909537479419 25000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16351/25000 : ℝ)) (X := (4281001909537479419/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s5_corner0a : (29281001909537479419/25000000000000000000 : ℝ) ≤ (10387626188087111/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (29281001909537479419/25000000000000000000 : ℝ)^32 ≤ (10387626188087111/10000000000000000 : ℝ)^133 := by
      have hnat : (29281001909537479419 : ℕ)^32*10000000000000000^133 ≤ 10387626188087111^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29281001909537479419 25000000000000000000 10387626188087111 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10387626188087111/10000000000000000 : ℝ)) (X := (29281001909537479419/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s5_corner0b : (16781001909537479419/12500000000000000000 : ℝ) ≤ (1073432714106111/1000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (16781001909537479419/12500000000000000000 : ℝ)^32 ≤ (1073432714106111/1000000000000000 : ℝ)^133 := by
      have hnat : (16781001909537479419 : ℕ)^32*1000000000000000^133 ≤ 1073432714106111^133*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16781001909537479419 12500000000000000000 1073432714106111 1000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1073432714106111/1000000000000000 : ℝ)) (X := (16781001909537479419/12500000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s5_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(387626188087111/6540400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(346700952973999/6540400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (16351/25000 : ℝ)) (alpha := (387626188087111/6540400000000000 : ℝ)) (beta := (346700952973999/6540400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow0,s5_corner0a]) (by linarith only [s5_pow0,s5_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (16351/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(387626188087111/6540400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(346700952973999/6540400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow1 : (66141/100000 : ℝ) ^ (133/32 : ℝ) ≤ (8970188870511491221/50000000000000000000 : ℝ) := by
    have hpowers : (66141/100000 : ℝ)^133 ≤ (8970188870511491221/50000000000000000000 : ℝ)^32 := by
      have hnat : (66141 : ℕ)^133*50000000000000000000^32 ≤ 8970188870511491221^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        66141 100000 8970188870511491221 50000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (66141/100000 : ℝ)) (X := (8970188870511491221/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s5_corner1a : (58970188870511491221/50000000000000000000 : ℝ) ≤ (2081000115873107/2000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (58970188870511491221/50000000000000000000 : ℝ)^32 ≤ (2081000115873107/2000000000000000 : ℝ)^133 := by
      have hnat : (58970188870511491221 : ℕ)^32*2000000000000000^133 ≤ 2081000115873107^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        58970188870511491221 50000000000000000000 2081000115873107 2000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2081000115873107/2000000000000000 : ℝ)) (X := (58970188870511491221/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s5_corner1b : (33970188870511491221/25000000000000000000 : ℝ) ≤ (2153118831401841/2000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (33970188870511491221/25000000000000000000 : ℝ)^32 ≤ (2153118831401841/2000000000000000 : ℝ)^133 := by
      have hnat : (33970188870511491221 : ℕ)^32*2000000000000000^133 ≤ 2153118831401841^133*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33970188870511491221 25000000000000000000 2153118831401841 2000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2153118831401841/2000000000000000 : ℝ)) (X := (33970188870511491221/25000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s5_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(27000038624369/440940000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(36059357764367/661410000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (66141/100000 : ℝ)) (alpha := (27000038624369/440940000000000 : ℝ)) (beta := (36059357764367/661410000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow1,s5_corner1a]) (by linarith only [s5_pow1,s5_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (66141/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(27000038624369/440940000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(36059357764367/661410000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow2 : (15883/25000 : ℝ) ^ (133/32 : ℝ) ≤ (15177061406411609703/100000000000000000000 : ℝ) := by
    have hpowers : (15883/25000 : ℝ)^133 ≤ (15177061406411609703/100000000000000000000 : ℝ)^32 := by
      have hnat : (15883 : ℕ)^133*100000000000000000000^32 ≤ 15177061406411609703^32*25000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15883 25000 15177061406411609703 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15883/25000 : ℝ)) (X := (15177061406411609703/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s5_corner2a : (115177061406411609703/100000000000000000000 : ℝ) ≤ (646613500263807/625000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (115177061406411609703/100000000000000000000 : ℝ)^32 ≤ (646613500263807/625000000000000 : ℝ)^133 := by
      have hnat : (115177061406411609703 : ℕ)^32*625000000000000^133 ≤ 646613500263807^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        115177061406411609703 100000000000000000000 646613500263807 625000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (646613500263807/625000000000000 : ℝ)) (X := (115177061406411609703/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have s5_corner2b : (65177061406411609703/50000000000000000000 : ℝ) ≤ (10658576169319181/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (65177061406411609703/50000000000000000000 : ℝ)^32 ≤ (10658576169319181/10000000000000000 : ℝ)^133 := by
      have hnat : (65177061406411609703 : ℕ)^32*10000000000000000^133 ≤ 10658576169319181^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65177061406411609703 50000000000000000000 10658576169319181 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10658576169319181/10000000000000000 : ℝ)) (X := (65177061406411609703/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have major_s5_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(21613500263807/397075000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(44680023585467/907600000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (133/32 : ℝ)) (rho := (15883/25000 : ℝ)) (alpha := (21613500263807/397075000000000 : ℝ)) (beta := (44680023585467/907600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow2,s5_corner2a]) (by linarith only [s5_pow2,s5_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (15883/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(21613500263807/397075000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(44680023585467/907600000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s5_0 : ((-252383217/2000000000 : ℝ)*X 0 0+(1387968147/2500000000 : ℝ)*X 0 1+(2825634321/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s5_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_1 : ((5553121401/10000000000 : ℝ)*X 1 0+(-1277437099/10000000000 : ℝ)*X 1 1+(2820153737/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s5_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_2 : ((5602495189/10000000000 : ℝ)*X 2 0+(5624740969/10000000000 : ℝ)*X 2 1+(-122346921/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s5_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_6 : ((4427154819/10000000000 : ℝ)*X 0 0+(4350213457/10000000000 : ℝ)*X 0 1+(2110866311/5000000000 : ℝ)*X 0 2+(4427154819/10000000000 : ℝ)*X 1 0+(4350213457/10000000000 : ℝ)*X 1 1+(2110866311/5000000000 : ℝ)*X 1 2+(4427154819/10000000000 : ℝ)*X 2 0+(4350213457/10000000000 : ℝ)*X 2 1+(2110866311/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s5_s5_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_7 : ((-968037909/10000000000 : ℝ)*X 0 0+(1117271677/2500000000 : ℝ)*X 0 1+(3416474603/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s5_s5_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_8 : ((4839085987/10000000000 : ℝ)*X 1 0+(-291199691/10000000000 : ℝ)*X 1 1+(3410866321/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s5_s5_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_9 : ((4574914851/10000000000 : ℝ)*X 2 0+(3543331531/5000000000 : ℝ)*X 2 1+(-8085369/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s5_s5_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_13 : ((275588751/625000000 : ℝ)*X 0 0+(6197944361/10000000000 : ℝ)*X 0 1+(1030255107/5000000000 : ℝ)*X 0 2+(275588751/625000000 : ℝ)*X 1 0+(6197944361/10000000000 : ℝ)*X 1 1+(1030255107/5000000000 : ℝ)*X 1 2+(275588751/625000000 : ℝ)*X 2 0+(6197944361/10000000000 : ℝ)*X 2 1+(1030255107/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s5_s5_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_14 : ((-258735203/10000000000 : ℝ)*X 0 0+(4856011731/10000000000 : ℝ)*X 0 1+(681837993/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s5_s5_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_15 : ((4506073081/10000000000 : ℝ)*X 1 0+(-19114899/200000000 : ℝ)*X 1 1+(6807163597/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s5_s5_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_16 : ((1691444757/2500000000 : ℝ)*X 2 0+(4930581199/10000000000 : ℝ)*X 2 1+(-27087853/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s5_s5_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_20 : ((3424596443/5000000000 : ℝ)*X 0 0+(1813326921/5000000000 : ℝ)*X 0 1+(52262577/250000000 : ℝ)*X 0 2+(3424596443/5000000000 : ℝ)*X 1 0+(1813326921/5000000000 : ℝ)*X 1 1+(52262577/250000000 : ℝ)*X 1 2+(3424596443/5000000000 : ℝ)*X 2 0+(1813326921/5000000000 : ℝ)*X 2 1+(52262577/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s5_s5_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_21 : ((-10443267/500000000 : ℝ)*X 0 0+(1593221093/2500000000 : ℝ)*X 0 1+(5357704257/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s5_s5_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_22 : ((6765125703/10000000000 : ℝ)*X 1 0+(-102456497/5000000000 : ℝ)*X 1 1+(493568719/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s5_s5_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_23 : ((560258453/1250000000 : ℝ)*X 2 0+(3429127139/5000000000 : ℝ)*X 2 1+(-899535603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s5_s5_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_27 : ((7002618327/10000000000 : ℝ)*X 0 0+(2926679161/10000000000 : ℝ)*X 0 1+(265049463/1000000000 : ℝ)*X 0 2+(7002618327/10000000000 : ℝ)*X 1 0+(2926679161/10000000000 : ℝ)*X 1 1+(265049463/1000000000 : ℝ)*X 1 2+(7002618327/10000000000 : ℝ)*X 2 0+(2926679161/10000000000 : ℝ)*X 2 1+(265049463/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c305063_s5_s5_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s5_0 : (0 : ℝ) ≤ ((26183/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26183/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (69675056400309935727195211/10004928600000000000000000000000 : ℝ) := by norm_num
    linear_combination (1274739/250000000000 : ℝ)*(base23) + (141227727253/1000000000000 : ℝ)*(base60) + (3333868410653/1000000000000 : ℝ)*(major_s5_0) + (3333868410653/1000000000000 : ℝ)*(major_s5_1) + (3333868410653/1000000000000 : ℝ)*(major_s5_2) + (473241/200000000000 : ℝ)*(sp_s5_0) + (2389421/250000000000 : ℝ)*(sp_s5_6) + (560960900697/125000000000 : ℝ)*(sp_s5_7) + (4487671037561/1000000000000 : ℝ)*(sp_s5_8) + (4487673541951/1000000000000 : ℝ)*(sp_s5_9) + (2180015297577/1000000000000 : ℝ)*(sp_s5_13) + (20072899/1000000000000 : ℝ)*(sp_s5_14) + (19303559/500000000000 : ℝ)*(sp_s5_15) + (7750943/250000000000 : ℝ)*(sp_s5_23) + (109001242763/50000000000 : ℝ)*(f.failure) + (4487709644679/1000000000000 : ℝ)*(f.sum) + (5857151859572898517/35017250100000000000000000000000 : ℝ)*base62 + (271966980625569/907600000000000000000000000 : ℝ)*base64 + (156661065059291/661410000000000000000000000 : ℝ)*base66 + (206034064117347/794150000000000000000000000 : ℝ)*base69 + (158281262909277941/463755237500000000000000000000 : ℝ)*base70 + (2782084023633987/6540400000000000000000000000 : ℝ)*base73 + (30737171683999/440940000000000000000000000 : ℝ)*base75 + (2338913026892963/6540400000000000000000000000 : ℝ)*base77 + (56744031489555661433/432588596400000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (617/625000000000000 : ℝ)*base86 + (617/625000000000000 : ℝ)*base88 + (617/625000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s5_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(53271/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(53271/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (479049330459148163188390663/72098099400000000000000000000000 : ℝ) := by norm_num
    linear_combination (5587877/1000000000000 : ℝ)*(base21) + (164707/1000000000000 : ℝ)*(base49) + (22673/100000000000 : ℝ)*(base60) + (3362736413383/1000000000000 : ℝ)*(major_s5_0) + (3362736413383/1000000000000 : ℝ)*(major_s5_1) + (3362736413383/1000000000000 : ℝ)*(major_s5_2) + (10218763/500000000000 : ℝ)*(sp_s5_2) + (31775563/1000000000000 : ℝ)*(sp_s5_7) + (5484433/250000000000 : ℝ)*(sp_s5_8) + (565817140283/125000000000 : ℝ)*(sp_s5_14) + (141454592503/31250000000 : ℝ)*(sp_s5_15) + (565817859053/125000000000 : ℝ)*(sp_s5_16) + (87954961/40000000 : ℝ)*(sp_s5_20) + (27689129/1000000000000 : ℝ)*(sp_s5_27) + (2198901714129/1000000000000 : ℝ)*(f.failure) + (1131642224457/250000000000 : ℝ)*(f.sum) + (1915364538149884307/35017250100000000000000000000000 : ℝ)*base62 + (386370557343541/907600000000000000000000000 : ℝ)*base65 + (632207360096273/661410000000000000000000000 : ℝ)*base67 + (210460686567317/794150000000000000000000000 : ℝ)*base69 + (523436257708545889/1855020950000000000000000000000 : ℝ)*base70 + (966190488603577/6540400000000000000000000000 : ℝ)*base73 + (269135082568241/440940000000000000000000000 : ℝ)*base75 + (4721196845506953/6540400000000000000000000000 : ℝ)*base77 + (7016976492227829677/432588596400000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (77/390625000000000 : ℝ)*base87 + (77/390625000000000 : ℝ)*base89 + (77/390625000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s5_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(50937/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(50937/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (132722513848340737881905846671/20448823442325000000000000000000000 : ℝ) := by norm_num
    linear_combination (457921/125000000000 : ℝ)*(base15) + (35208135869/200000000000 : ℝ)*(base40) + (2737627/1000000000000 : ℝ)*(base59) + (1591734890873/500000000000 : ℝ)*(major_s5_0) + (1591734890873/500000000000 : ℝ)*(major_s5_1) + (1591734890873/500000000000 : ℝ)*(major_s5_2) + (116027/1000000000000 : ℝ)*(sp_s5_1) + (3345991/250000000000 : ℝ)*(sp_s5_2) + (14599987/500000000000 : ℝ)*(sp_s5_9) + (63518857/1000000000000 : ℝ)*(sp_s5_20) + (4285258582681/1000000000000 : ℝ)*(sp_s5_21) + (2142627401643/500000000000 : ℝ)*(sp_s5_22) + (4285215998743/1000000000000 : ℝ)*(sp_s5_23) + (2081615298459/1000000000000 : ℝ)*(sp_s5_27) + (2081678817317/1000000000000 : ℝ)*(f.failure) + (4285258582681/1000000000000 : ℝ)*(f.sum) + (2121535052177726537/4377156262500000000000000000000 : ℝ)*base63 + (278112053055809/453800000000000000000000000 : ℝ)*base64 + (20107748573909/132282000000000000000000000 : ℝ)*base66 + (5081858686789/198537500000000000000000000 : ℝ)*base68 + (13419104426550577/463755237500000000000000000000 : ℝ)*base70 + (542012329362233/3270200000000000000000000000 : ℝ)*base72 + (18383883451289/110235000000000000000000000 : ℝ)*base75 + (414546124349883/3270200000000000000000000000 : ℝ)*base77 + (13638870724009929473/216294298200000000000000000000000 : ℝ)*base78 + (1693/3125000000000000 : ℝ)*base87 + (1693/3125000000000000 : ℝ)*base89 + (1693/3125000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  exact ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (67/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4779/3125 : ℝ) (93447/50000 : ℝ) (76771/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev4 : (0 : ℝ) ≤ ((16351/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(16351/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(66141/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(66141/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15883/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15883/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((26183/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26183/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(53271/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(53271/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(50937/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(50937/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c305063_s5 p hpa hpb X hX hprev4

#print axioms solution
