-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c329061_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:28:39.808642+00:00
-- url     : https://prove2.me/submissions/7bbb53f8-4b8f-422b-b496-6c5410077d2b

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
theorem collision_support_c329061_s1_s1_0 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1741180821/10000000000 : ℝ)*x 0 + (2181675327/5000000000 : ℝ)*x 1 + (1140485419/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1741180821/10000000000 : ℝ)^95 ≤ (611027476403/5000000000000 : ℝ)^79 := by
    have hnat : (1741180821 : ℕ)^95*5000000000000^79 ≤ 611027476403^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1741180821 10000000000 611027476403 5000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2181675327/5000000000 : ℝ)^95 ≤ (18443455639459/50000000000000 : ℝ)^79 := by
    have hnat : (2181675327 : ℕ)^95*50000000000000^79 ≤ 18443455639459^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181675327 5000000000 18443455639459 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1140485419/2000000000 : ℝ)^95 ≤ (50892539174497/100000000000000 : ℝ)^79 := by
    have hnat : (1140485419 : ℕ)^95*100000000000000^79 ≤ 50892539174497^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140485419 2000000000 50892539174497 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1741180821/10000000000 : ℝ), (2181675327/5000000000 : ℝ), (1140485419/2000000000 : ℝ)] ![(611027476403/5000000000000 : ℝ), (18443455639459/50000000000000 : ℝ), (50892539174497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1741180821/10000000000 : ℝ)|^95 ≤ (611027476403/5000000000000 : ℝ)^79
        have hw : |(-1741180821/10000000000 : ℝ)|=(1741180821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2181675327/5000000000 : ℝ)|^95 ≤ (18443455639459/50000000000000 : ℝ)^79
        have hw : |(2181675327/5000000000 : ℝ)|=(2181675327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1140485419/2000000000 : ℝ)|^95 ≤ (50892539174497/100000000000000 : ℝ)^79
        have hw : |(1140485419/2000000000 : ℝ)|=(1140485419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329061_s1_s1_1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4599167893/10000000000 : ℝ)*x 0 + (-1744378179/10000000000 : ℝ)*x 1 + (5474399067/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4599167893/10000000000 : ℝ)^95 ≤ (9824289432763/25000000000000 : ℝ)^79 := by
    have hnat : (4599167893 : ℕ)^95*25000000000000^79 ≤ 9824289432763^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4599167893 10000000000 9824289432763 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1744378179/10000000000 : ℝ)^95 ≤ (6123770151483/50000000000000 : ℝ)^79 := by
    have hnat : (1744378179 : ℕ)^95*50000000000000^79 ≤ 6123770151483^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1744378179 10000000000 6123770151483 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5474399067/10000000000 : ℝ)^95 ≤ (12113825486901/25000000000000 : ℝ)^79 := by
    have hnat : (5474399067 : ℕ)^95*25000000000000^79 ≤ 12113825486901^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474399067 10000000000 12113825486901 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4599167893/10000000000 : ℝ), (-1744378179/10000000000 : ℝ), (5474399067/10000000000 : ℝ)] ![(9824289432763/25000000000000 : ℝ), (6123770151483/50000000000000 : ℝ), (12113825486901/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4599167893/10000000000 : ℝ)|^95 ≤ (9824289432763/25000000000000 : ℝ)^79
        have hw : |(4599167893/10000000000 : ℝ)|=(4599167893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1744378179/10000000000 : ℝ)|^95 ≤ (6123770151483/50000000000000 : ℝ)^79
        have hw : |(-1744378179/10000000000 : ℝ)|=(1744378179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5474399067/10000000000 : ℝ)|^95 ≤ (12113825486901/25000000000000 : ℝ)^79
        have hw : |(5474399067/10000000000 : ℝ)|=(5474399067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329061_s1_s1_2 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (578906347/1250000000 : ℝ)*x 0 + (6088826263/10000000000 : ℝ)*x 1 + (-217496019/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (578906347/1250000000 : ℝ)^95 ≤ (39627039179491/100000000000000 : ℝ)^79 := by
    have hnat : (578906347 : ℕ)^95*100000000000000^79 ≤ 39627039179491^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      578906347 1250000000 39627039179491 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6088826263/10000000000 : ℝ)^95 ≤ (55067430711651/100000000000000 : ℝ)^79 := by
    have hnat : (6088826263 : ℕ)^95*100000000000000^79 ≤ 55067430711651^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6088826263 10000000000 55067430711651 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217496019/2500000000 : ℝ)^95 ≤ (2652765049203/50000000000000 : ℝ)^79 := by
    have hnat : (217496019 : ℕ)^95*50000000000000^79 ≤ 2652765049203^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217496019 2500000000 2652765049203 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(578906347/1250000000 : ℝ), (6088826263/10000000000 : ℝ), (-217496019/2500000000 : ℝ)] ![(39627039179491/100000000000000 : ℝ), (55067430711651/100000000000000 : ℝ), (2652765049203/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(578906347/1250000000 : ℝ)|^95 ≤ (39627039179491/100000000000000 : ℝ)^79
        have hw : |(578906347/1250000000 : ℝ)|=(578906347/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6088826263/10000000000 : ℝ)|^95 ≤ (55067430711651/100000000000000 : ℝ)^79
        have hw : |(6088826263/10000000000 : ℝ)|=(6088826263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-217496019/2500000000 : ℝ)|^95 ≤ (2652765049203/50000000000000 : ℝ)^79
        have hw : |(-217496019/2500000000 : ℝ)|=(217496019/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329061_s1_s1_6 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6572579469/10000000000 : ℝ)*x 0 + (1170643153/5000000000 : ℝ)*x 1 + (2858543187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6572579469/10000000000 : ℝ)^95 ≤ (60370057123763/100000000000000 : ℝ)^79 := by
    have hnat : (6572579469 : ℕ)^95*100000000000000^79 ≤ 60370057123763^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6572579469 10000000000 60370057123763 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1170643153/5000000000 : ℝ)^95 ≤ (4362034749403/25000000000000 : ℝ)^79 := by
    have hnat : (1170643153 : ℕ)^95*25000000000000^79 ≤ 4362034749403^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1170643153 5000000000 4362034749403 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2858543187/10000000000 : ℝ)^95 ≤ (5545450965497/25000000000000 : ℝ)^79 := by
    have hnat : (2858543187 : ℕ)^95*25000000000000^79 ≤ 5545450965497^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2858543187 10000000000 5545450965497 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6572579469/10000000000 : ℝ), (1170643153/5000000000 : ℝ), (2858543187/10000000000 : ℝ)] ![(60370057123763/100000000000000 : ℝ), (4362034749403/25000000000000 : ℝ), (5545450965497/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6572579469/10000000000 : ℝ)|^95 ≤ (60370057123763/100000000000000 : ℝ)^79
        have hw : |(6572579469/10000000000 : ℝ)|=(6572579469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1170643153/5000000000 : ℝ)|^95 ≤ (4362034749403/25000000000000 : ℝ)^79
        have hw : |(1170643153/5000000000 : ℝ)|=(1170643153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2858543187/10000000000 : ℝ)|^95 ≤ (5545450965497/25000000000000 : ℝ)^79
        have hw : |(2858543187/10000000000 : ℝ)|=(2858543187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329061_s1_s1_7 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-887469089/5000000000 : ℝ)*x 0 + (4134774719/10000000000 : ℝ)*x 1 + (235622201/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (887469089/5000000000 : ℝ)^95 ≤ (6253009371081/50000000000000 : ℝ)^79 := by
    have hnat : (887469089 : ℕ)^95*50000000000000^79 ≤ 6253009371081^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      887469089 5000000000 6253009371081 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4134774719/10000000000 : ℝ)^95 ≤ (17287859289159/50000000000000 : ℝ)^79 := by
    have hnat : (4134774719 : ℕ)^95*50000000000000^79 ≤ 17287859289159^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4134774719 10000000000 17287859289159 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (235622201/400000000 : ℝ)^95 ≤ (52918262665279/100000000000000 : ℝ)^79 := by
    have hnat : (235622201 : ℕ)^95*100000000000000^79 ≤ 52918262665279^79*400000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235622201 400000000 52918262665279 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-887469089/5000000000 : ℝ), (4134774719/10000000000 : ℝ), (235622201/400000000 : ℝ)] ![(6253009371081/50000000000000 : ℝ), (17287859289159/50000000000000 : ℝ), (52918262665279/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-887469089/5000000000 : ℝ)|^95 ≤ (6253009371081/50000000000000 : ℝ)^79
        have hw : |(-887469089/5000000000 : ℝ)|=(887469089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4134774719/10000000000 : ℝ)|^95 ≤ (17287859289159/50000000000000 : ℝ)^79
        have hw : |(4134774719/10000000000 : ℝ)|=(4134774719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(235622201/400000000 : ℝ)|^95 ≤ (52918262665279/100000000000000 : ℝ)^79
        have hw : |(235622201/400000000 : ℝ)|=(235622201/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329061_s1_s1_8 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (883017983/2000000000 : ℝ)*x 0 + (-35751191/250000000 : ℝ)*x 1 + (2946372557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (883017983/2000000000 : ℝ)^95 ≤ (584586257753/1562500000000 : ℝ)^79 := by
    have hnat : (883017983 : ℕ)^95*1562500000000^79 ≤ 584586257753^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      883017983 2000000000 584586257753 1562500000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35751191/250000000 : ℝ)^95 ≤ (964455632123/10000000000000 : ℝ)^79 := by
    have hnat : (35751191 : ℕ)^95*10000000000000^79 ≤ 964455632123^79*250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35751191 250000000 964455632123 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2946372557/5000000000 : ℝ)^95 ≤ (13235480792269/25000000000000 : ℝ)^79 := by
    have hnat : (2946372557 : ℕ)^95*25000000000000^79 ≤ 13235480792269^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2946372557 5000000000 13235480792269 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(883017983/2000000000 : ℝ), (-35751191/250000000 : ℝ), (2946372557/5000000000 : ℝ)] ![(584586257753/1562500000000 : ℝ), (964455632123/10000000000000 : ℝ), (13235480792269/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(883017983/2000000000 : ℝ)|^95 ≤ (584586257753/1562500000000 : ℝ)^79
        have hw : |(883017983/2000000000 : ℝ)|=(883017983/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-35751191/250000000 : ℝ)|^95 ≤ (964455632123/10000000000000 : ℝ)^79
        have hw : |(-35751191/250000000 : ℝ)|=(35751191/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2946372557/5000000000 : ℝ)|^95 ≤ (13235480792269/25000000000000 : ℝ)^79
        have hw : |(2946372557/5000000000 : ℝ)|=(2946372557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329061_s1_s1_9 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4447236367/10000000000 : ℝ)*x 0 + (1629379223/2500000000 : ℝ)*x 1 + (-14523517/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4447236367/10000000000 : ℝ)^95 ≤ (3774134247177/10000000000000 : ℝ)^79 := by
    have hnat : (4447236367 : ℕ)^95*10000000000000^79 ≤ 3774134247177^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4447236367 10000000000 3774134247177 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1629379223/2500000000 : ℝ)^95 ≤ (29881192463399/50000000000000 : ℝ)^79 := by
    have hnat : (1629379223 : ℕ)^95*50000000000000^79 ≤ 29881192463399^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1629379223 2500000000 29881192463399 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (14523517/312500000 : ℝ)^95 ≤ (2496272594277/100000000000000 : ℝ)^79 := by
    have hnat : (14523517 : ℕ)^95*100000000000000^79 ≤ 2496272594277^79*312500000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      14523517 312500000 2496272594277 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4447236367/10000000000 : ℝ), (1629379223/2500000000 : ℝ), (-14523517/312500000 : ℝ)] ![(3774134247177/10000000000000 : ℝ), (29881192463399/50000000000000 : ℝ), (2496272594277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4447236367/10000000000 : ℝ)|^95 ≤ (3774134247177/10000000000000 : ℝ)^79
        have hw : |(4447236367/10000000000 : ℝ)|=(4447236367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1629379223/2500000000 : ℝ)|^95 ≤ (29881192463399/50000000000000 : ℝ)^79
        have hw : |(1629379223/2500000000 : ℝ)|=(1629379223/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-14523517/312500000 : ℝ)|^95 ≤ (2496272594277/100000000000000 : ℝ)^79
        have hw : |(-14523517/312500000 : ℝ)|=(14523517/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329061_s1_s1_13 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1335306007/2000000000 : ℝ)*x 0 + (2821919429/10000000000 : ℝ)*x 1 + (90027519/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1335306007/2000000000 : ℝ)^95 ≤ (12304013216517/20000000000000 : ℝ)^79 := by
    have hnat : (1335306007 : ℕ)^95*20000000000000^79 ≤ 12304013216517^79*2000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1335306007 2000000000 12304013216517 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2821919429/10000000000 : ℝ)^95 ≤ (21840496417487/100000000000000 : ℝ)^79 := by
    have hnat : (2821919429 : ℕ)^95*100000000000000^79 ≤ 21840496417487^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2821919429 10000000000 21840496417487 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90027519/400000000 : ℝ)^95 ≤ (2079929686563/12500000000000 : ℝ)^79 := by
    have hnat : (90027519 : ℕ)^95*12500000000000^79 ≤ 2079929686563^79*400000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90027519 400000000 2079929686563 12500000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1335306007/2000000000 : ℝ), (2821919429/10000000000 : ℝ), (90027519/400000000 : ℝ)] ![(12304013216517/20000000000000 : ℝ), (21840496417487/100000000000000 : ℝ), (2079929686563/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1335306007/2000000000 : ℝ)|^95 ≤ (12304013216517/20000000000000 : ℝ)^79
        have hw : |(1335306007/2000000000 : ℝ)|=(1335306007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2821919429/10000000000 : ℝ)|^95 ≤ (21840496417487/100000000000000 : ℝ)^79
        have hw : |(2821919429/10000000000 : ℝ)|=(2821919429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(90027519/400000000 : ℝ)|^95 ≤ (2079929686563/12500000000000 : ℝ)^79
        have hw : |(90027519/400000000 : ℝ)|=(90027519/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329061_s1_s1_14 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-576326149/5000000000 : ℝ)*x 0 + (2315604951/5000000000 : ℝ)*x 1 + (5891812381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (576326149/5000000000 : ℝ)^95 ≤ (1860383786503/25000000000000 : ℝ)^79 := by
    have hnat : (576326149 : ℕ)^95*25000000000000^79 ≤ 1860383786503^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      576326149 5000000000 1860383786503 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2315604951/5000000000 : ℝ)^95 ≤ (7925323722227/20000000000000 : ℝ)^79 := by
    have hnat : (2315604951 : ℕ)^95*20000000000000^79 ≤ 7925323722227^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2315604951 5000000000 7925323722227 20000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5891812381/10000000000 : ℝ)^95 ≤ (26465923111301/50000000000000 : ℝ)^79 := by
    have hnat : (5891812381 : ℕ)^95*50000000000000^79 ≤ 26465923111301^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5891812381 10000000000 26465923111301 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-576326149/5000000000 : ℝ), (2315604951/5000000000 : ℝ), (5891812381/10000000000 : ℝ)] ![(1860383786503/25000000000000 : ℝ), (7925323722227/20000000000000 : ℝ), (26465923111301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-576326149/5000000000 : ℝ)|^95 ≤ (1860383786503/25000000000000 : ℝ)^79
        have hw : |(-576326149/5000000000 : ℝ)|=(576326149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2315604951/5000000000 : ℝ)|^95 ≤ (7925323722227/20000000000000 : ℝ)^79
        have hw : |(2315604951/5000000000 : ℝ)|=(2315604951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5891812381/10000000000 : ℝ)|^95 ≤ (26465923111301/50000000000000 : ℝ)^79
        have hw : |(5891812381/10000000000 : ℝ)|=(5891812381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329061_s1_s1_15 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4364274183/10000000000 : ℝ)*x 0 + (-372968759/2500000000 : ℝ)*x 1 + (1473501463/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364274183/10000000000 : ℝ)^95 ≤ (36896300045339/100000000000000 : ℝ)^79 := by
    have hnat : (4364274183 : ℕ)^95*100000000000000^79 ≤ 36896300045339^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364274183 10000000000 36896300045339 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (372968759/2500000000 : ℝ)^95 ≤ (10148155647667/100000000000000 : ℝ)^79 := by
    have hnat : (372968759 : ℕ)^95*100000000000000^79 ≤ 10148155647667^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372968759 2500000000 10148155647667 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1473501463/2500000000 : ℝ)^95 ≤ (52955544289193/100000000000000 : ℝ)^79 := by
    have hnat : (1473501463 : ℕ)^95*100000000000000^79 ≤ 52955544289193^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1473501463 2500000000 52955544289193 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364274183/10000000000 : ℝ), (-372968759/2500000000 : ℝ), (1473501463/2500000000 : ℝ)] ![(36896300045339/100000000000000 : ℝ), (10148155647667/100000000000000 : ℝ), (52955544289193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364274183/10000000000 : ℝ)|^95 ≤ (36896300045339/100000000000000 : ℝ)^79
        have hw : |(4364274183/10000000000 : ℝ)|=(4364274183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-372968759/2500000000 : ℝ)|^95 ≤ (10148155647667/100000000000000 : ℝ)^79
        have hw : |(-372968759/2500000000 : ℝ)|=(372968759/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1473501463/2500000000 : ℝ)|^95 ≤ (52955544289193/100000000000000 : ℝ)^79
        have hw : |(1473501463/2500000000 : ℝ)|=(1473501463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329061_s1_s1_16 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1308238763/2500000000 : ℝ)*x 0 + (721206077/1250000000 : ℝ)*x 1 + (-231747801/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1308238763/2500000000 : ℝ)^95 ≤ (45897007720781/100000000000000 : ℝ)^79 := by
    have hnat : (1308238763 : ℕ)^95*100000000000000^79 ≤ 45897007720781^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308238763 2500000000 45897007720781 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (721206077/1250000000 : ℝ)^95 ≤ (3225927253563/6250000000000 : ℝ)^79 := by
    have hnat : (721206077 : ℕ)^95*6250000000000^79 ≤ 3225927253563^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      721206077 1250000000 3225927253563 6250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (231747801/5000000000 : ℝ)^95 ≤ (1244078101833/50000000000000 : ℝ)^79 := by
    have hnat : (231747801 : ℕ)^95*50000000000000^79 ≤ 1244078101833^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      231747801 5000000000 1244078101833 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1308238763/2500000000 : ℝ), (721206077/1250000000 : ℝ), (-231747801/5000000000 : ℝ)] ![(45897007720781/100000000000000 : ℝ), (3225927253563/6250000000000 : ℝ), (1244078101833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1308238763/2500000000 : ℝ)|^95 ≤ (45897007720781/100000000000000 : ℝ)^79
        have hw : |(1308238763/2500000000 : ℝ)|=(1308238763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(721206077/1250000000 : ℝ)|^95 ≤ (3225927253563/6250000000000 : ℝ)^79
        have hw : |(721206077/1250000000 : ℝ)|=(721206077/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-231747801/5000000000 : ℝ)|^95 ≤ (1244078101833/50000000000000 : ℝ)^79
        have hw : |(-231747801/5000000000 : ℝ)|=(231747801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329061_s1_s1_20 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1853765349/2500000000 : ℝ)*x 0 + (1903893491/10000000000 : ℝ)*x 1 + (2246357663/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1853765349/2500000000 : ℝ)^95 ≤ (87240649689/125000000000 : ℝ)^79 := by
    have hnat : (1853765349 : ℕ)^95*125000000000^79 ≤ 87240649689^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1853765349 2500000000 87240649689 125000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1903893491/10000000000 : ℝ)^95 ≤ (3401633329403/25000000000000 : ℝ)^79 := by
    have hnat : (1903893491 : ℕ)^95*25000000000000^79 ≤ 3401633329403^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1903893491 10000000000 3401633329403 25000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2246357663/10000000000 : ℝ)^95 ≤ (16600946918723/100000000000000 : ℝ)^79 := by
    have hnat : (2246357663 : ℕ)^95*100000000000000^79 ≤ 16600946918723^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2246357663 10000000000 16600946918723 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1853765349/2500000000 : ℝ), (1903893491/10000000000 : ℝ), (2246357663/10000000000 : ℝ)] ![(87240649689/125000000000 : ℝ), (3401633329403/25000000000000 : ℝ), (16600946918723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1853765349/2500000000 : ℝ)|^95 ≤ (87240649689/125000000000 : ℝ)^79
        have hw : |(1853765349/2500000000 : ℝ)|=(1853765349/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1903893491/10000000000 : ℝ)|^95 ≤ (3401633329403/25000000000000 : ℝ)^79
        have hw : |(1903893491/10000000000 : ℝ)|=(1903893491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2246357663/10000000000 : ℝ)|^95 ≤ (16600946918723/100000000000000 : ℝ)^79
        have hw : |(2246357663/10000000000 : ℝ)|=(2246357663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329061_s1_s1_21 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-118448497/1000000000 : ℝ)*x 0 + (4773130313/10000000000 : ℝ)*x 1 + (716606669/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (118448497/1000000000 : ℝ)^95 ≤ (384467801889/5000000000000 : ℝ)^79 := by
    have hnat : (118448497 : ℕ)^95*5000000000000^79 ≤ 384467801889^79*1000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      118448497 1000000000 384467801889 5000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4773130313/10000000000 : ℝ)^95 ≤ (20545693155203/50000000000000 : ℝ)^79 := by
    have hnat : (4773130313 : ℕ)^95*50000000000000^79 ≤ 20545693155203^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4773130313 10000000000 20545693155203 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (716606669/1250000000 : ℝ)^95 ≤ (25609628821419/50000000000000 : ℝ)^79 := by
    have hnat : (716606669 : ℕ)^95*50000000000000^79 ≤ 25609628821419^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      716606669 1250000000 25609628821419 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-118448497/1000000000 : ℝ), (4773130313/10000000000 : ℝ), (716606669/1250000000 : ℝ)] ![(384467801889/5000000000000 : ℝ), (20545693155203/50000000000000 : ℝ), (25609628821419/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-118448497/1000000000 : ℝ)|^95 ≤ (384467801889/5000000000000 : ℝ)^79
        have hw : |(-118448497/1000000000 : ℝ)|=(118448497/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4773130313/10000000000 : ℝ)|^95 ≤ (20545693155203/50000000000000 : ℝ)^79
        have hw : |(4773130313/10000000000 : ℝ)|=(4773130313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(716606669/1250000000 : ℝ)|^95 ≤ (25609628821419/50000000000000 : ℝ)^79
        have hw : |(716606669/1250000000 : ℝ)|=(716606669/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329061_s1_s1_22 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5168974679/10000000000 : ℝ)*x 0 + (-296694613/2500000000 : ℝ)*x 1 + (2671952051/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5168974679/10000000000 : ℝ)^95 ≤ (22611518640819/50000000000000 : ℝ)^79 := by
    have hnat : (5168974679 : ℕ)^95*50000000000000^79 ≤ 22611518640819^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5168974679 10000000000 22611518640819 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (296694613/2500000000 : ℝ)^95 ≤ (3853631818569/50000000000000 : ℝ)^79 := by
    have hnat : (296694613 : ℕ)^95*50000000000000^79 ≤ 3853631818569^79*2500000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      296694613 2500000000 3853631818569 50000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2671952051/5000000000 : ℝ)^95 ≤ (73546404799/156250000000 : ℝ)^79 := by
    have hnat : (2671952051 : ℕ)^95*156250000000^79 ≤ 73546404799^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2671952051 5000000000 73546404799 156250000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5168974679/10000000000 : ℝ), (-296694613/2500000000 : ℝ), (2671952051/5000000000 : ℝ)] ![(22611518640819/50000000000000 : ℝ), (3853631818569/50000000000000 : ℝ), (73546404799/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5168974679/10000000000 : ℝ)|^95 ≤ (22611518640819/50000000000000 : ℝ)^79
        have hw : |(5168974679/10000000000 : ℝ)|=(5168974679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-296694613/2500000000 : ℝ)|^95 ≤ (3853631818569/50000000000000 : ℝ)^79
        have hw : |(-296694613/2500000000 : ℝ)|=(296694613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2671952051/5000000000 : ℝ)|^95 ≤ (73546404799/156250000000 : ℝ)^79
        have hw : |(2671952051/5000000000 : ℝ)|=(2671952051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329061_s1_s1_23 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (541241557/1250000000 : ℝ)*x 0 + (3209241323/5000000000 : ℝ)*x 1 + (-398884657/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541241557/1250000000 : ℝ)^95 ≤ (36547447010007/100000000000000 : ℝ)^79 := by
    have hnat : (541241557 : ℕ)^95*100000000000000^79 ≤ 36547447010007^79*1250000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541241557 1250000000 36547447010007 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3209241323/5000000000 : ℝ)^95 ≤ (3667003714993/6250000000000 : ℝ)^79 := by
    have hnat : (3209241323 : ℕ)^95*6250000000000^79 ≤ 3667003714993^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3209241323 5000000000 3667003714993 6250000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (398884657/5000000000 : ℝ)^95 ≤ (4780493536277/100000000000000 : ℝ)^79 := by
    have hnat : (398884657 : ℕ)^95*100000000000000^79 ≤ 4780493536277^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398884657 5000000000 4780493536277 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541241557/1250000000 : ℝ), (3209241323/5000000000 : ℝ), (-398884657/5000000000 : ℝ)] ![(36547447010007/100000000000000 : ℝ), (3667003714993/6250000000000 : ℝ), (4780493536277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541241557/1250000000 : ℝ)|^95 ≤ (36547447010007/100000000000000 : ℝ)^79
        have hw : |(541241557/1250000000 : ℝ)|=(541241557/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3209241323/5000000000 : ℝ)|^95 ≤ (3667003714993/6250000000000 : ℝ)^79
        have hw : |(3209241323/5000000000 : ℝ)|=(3209241323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-398884657/5000000000 : ℝ)|^95 ≤ (4780493536277/100000000000000 : ℝ)^79
        have hw : |(-398884657/5000000000 : ℝ)|=(398884657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c329061_s1_s1_27 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ)) (x : Fin 3 → ℝ) :
    (238883189/312500000 : ℝ)*x 0 + (900702813/5000000000 : ℝ)*x 1 + (2050325527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (238883189/312500000 : ℝ)^95 ≤ (72394792337933/100000000000000 : ℝ)^79 := by
    have hnat : (238883189 : ℕ)^95*100000000000000^79 ≤ 72394792337933^79*312500000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238883189 312500000 72394792337933 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (900702813/5000000000 : ℝ)^95 ≤ (12730612230573/100000000000000 : ℝ)^79 := by
    have hnat : (900702813 : ℕ)^95*100000000000000^79 ≤ 12730612230573^79*5000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900702813 5000000000 12730612230573 100000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2050325527/10000000000 : ℝ)^95 ≤ (1487459541393/10000000000000 : ℝ)^79 := by
    have hnat : (2050325527 : ℕ)^95*10000000000000^79 ≤ 1487459541393^79*10000000000^95 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2050325527 10000000000 1487459541393 10000000000000 95 79 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (95/16 : ℝ)) 95 79 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(238883189/312500000 : ℝ), (900702813/5000000000 : ℝ), (2050325527/10000000000 : ℝ)] ![(72394792337933/100000000000000 : ℝ), (12730612230573/100000000000000 : ℝ), (1487459541393/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(238883189/312500000 : ℝ)|^95 ≤ (72394792337933/100000000000000 : ℝ)^79
        have hw : |(238883189/312500000 : ℝ)|=(238883189/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(900702813/5000000000 : ℝ)|^95 ≤ (12730612230573/100000000000000 : ℝ)^79
        have hw : |(900702813/5000000000 : ℝ)|=(900702813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2050325527/10000000000 : ℝ)|^95 ≤ (1487459541393/10000000000000 : ℝ)^79
        have hw : |(2050325527/10000000000 : ℝ)|=(2050325527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c329061_s1 (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((60861/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(60861/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(60543/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(60543/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13897/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13897/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5197/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5197/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27251/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(27251/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12387/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12387/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (10347/12500 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (10347/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (10347/12500 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (10347/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (10347/12500 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  have s1_pow0 : (60861/100000 : ℝ) ^ (93/16 : ℝ) ≤ (5577902585247162941/100000000000000000000 : ℝ) := by
    have hpowers : (60861/100000 : ℝ)^93 ≤ (5577902585247162941/100000000000000000000 : ℝ)^16 := by
      have hnat : (60861 : ℕ)^93*100000000000000000000^16 ≤ 5577902585247162941^16*100000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60861 100000 5577902585247162941 100000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (60861/100000 : ℝ)) (X := (5577902585247162941/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (105577902585247162941/100000000000000000000 : ℝ) ≤ (10093820447040931/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (105577902585247162941/100000000000000000000 : ℝ)^16 ≤ (10093820447040931/10000000000000000 : ℝ)^93 := by
      have hnat : (105577902585247162941 : ℕ)^16*10000000000000000^93 ≤ 10093820447040931^93*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        105577902585247162941 100000000000000000000 10093820447040931 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10093820447040931/10000000000000000 : ℝ)) (X := (105577902585247162941/100000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (55577902585247162941/50000000000000000000 : ℝ) ≤ (10183622810539741/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (55577902585247162941/50000000000000000000 : ℝ)^16 ≤ (10183622810539741/10000000000000000 : ℝ)^93 := by
      have hnat : (55577902585247162941 : ℕ)^16*10000000000000000^93 ≤ 10183622810539741^93*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55577902585247162941 50000000000000000000 10183622810539741 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10183622810539741/10000000000000000 : ℝ)) (X := (55577902585247162941/50000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(31273482346977/2028700000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(2993412116627/202870000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (60861/100000 : ℝ)) (alpha := (31273482346977/2028700000000000 : ℝ)) (beta := (2993412116627/202870000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (60861/100000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(31273482346977/2028700000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(2993412116627/202870000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (60543/100000 : ℝ) ^ (93/16 : ℝ) ≤ (2705307514523095463/50000000000000000000 : ℝ) := by
    have hpowers : (60543/100000 : ℝ)^93 ≤ (2705307514523095463/50000000000000000000 : ℝ)^16 := by
      have hnat : (60543 : ℕ)^93*50000000000000000000^16 ≤ 2705307514523095463^16*100000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60543 100000 2705307514523095463 50000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (60543/100000 : ℝ)) (X := (2705307514523095463/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (52705307514523095463/50000000000000000000 : ℝ) ≤ (10091067053611541/10000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (52705307514523095463/50000000000000000000 : ℝ)^16 ≤ (10091067053611541/10000000000000000 : ℝ)^93 := by
      have hnat : (52705307514523095463 : ℕ)^16*10000000000000000^93 ≤ 10091067053611541^93*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52705307514523095463 50000000000000000000 10091067053611541 10000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10091067053611541/10000000000000000 : ℝ)) (X := (52705307514523095463/50000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (27705307514523095463/25000000000000000000 : ℝ) ≤ (5089171352296817/5000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (27705307514523095463/25000000000000000000 : ℝ)^16 ≤ (5089171352296817/5000000000000000 : ℝ)^93 := by
      have hnat : (27705307514523095463 : ℕ)^16*5000000000000000^93 ≤ 5089171352296817^93*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27705307514523095463 25000000000000000000 5089171352296817 5000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5089171352296817/5000000000000000 : ℝ)) (X := (27705307514523095463/25000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(13009579087363/864900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(12467950140299/864900000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (60543/100000 : ℝ)) (alpha := (13009579087363/864900000000000 : ℝ)) (beta := (12467950140299/864900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (60543/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(13009579087363/864900000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(12467950140299/864900000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (13897/25000 : ℝ) ^ (93/16 : ℝ) ≤ (1646919420323546873/50000000000000000000 : ℝ) := by
    have hpowers : (13897/25000 : ℝ)^93 ≤ (1646919420323546873/50000000000000000000 : ℝ)^16 := by
      have hnat : (13897 : ℕ)^93*50000000000000000000^16 ≤ 1646919420323546873^16*25000^93 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13897 25000 1646919420323546873 50000000000000000000 93 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13897/25000 : ℝ)) (X := (1646919420323546873/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (51646919420323546873/50000000000000000000 : ℝ) ≤ (5027955317963197/5000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (51646919420323546873/50000000000000000000 : ℝ)^16 ≤ (5027955317963197/5000000000000000 : ℝ)^93 := by
      have hnat : (51646919420323546873 : ℕ)^16*5000000000000000^93 ≤ 5027955317963197^93*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51646919420323546873 50000000000000000000 5027955317963197 5000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5027955317963197/5000000000000000 : ℝ)) (X := (51646919420323546873/50000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (26646919420323546873/25000000000000000000 : ℝ) ≤ (5055182047290789/5000000000000000 : ℝ) ^ (93/16 : ℝ) := by
    have hpowers : (26646919420323546873/25000000000000000000 : ℝ)^16 ≤ (5055182047290789/5000000000000000 : ℝ)^93 := by
      have hnat : (26646919420323546873 : ℕ)^16*5000000000000000^93 ≤ 5055182047290789^93*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26646919420323546873 25000000000000000000 5055182047290789 5000000000000000 16 93 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5055182047290789/5000000000000000 : ℝ)) (X := (26646919420323546873/25000000000000000000 : ℝ)) (by norm_num) 93 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(27955317963197/2779400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(3403341165949/347425000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (93/16 : ℝ)) (rho := (13897/25000 : ℝ)) (alpha := (27955317963197/2779400000000000 : ℝ)) (beta := (3403341165949/347425000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (13897/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(27955317963197/2779400000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(3403341165949/347425000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1741180821/10000000000 : ℝ)*X 0 0+(2181675327/5000000000 : ℝ)*X 0 1+(1140485419/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329061_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((4599167893/10000000000 : ℝ)*X 1 0+(-1744378179/10000000000 : ℝ)*X 1 1+(5474399067/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329061_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((578906347/1250000000 : ℝ)*X 2 0+(6088826263/10000000000 : ℝ)*X 2 1+(-217496019/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329061_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((6572579469/10000000000 : ℝ)*X 0 0+(1170643153/5000000000 : ℝ)*X 0 1+(2858543187/10000000000 : ℝ)*X 0 2+(6572579469/10000000000 : ℝ)*X 1 0+(1170643153/5000000000 : ℝ)*X 1 1+(2858543187/10000000000 : ℝ)*X 1 2+(6572579469/10000000000 : ℝ)*X 2 0+(1170643153/5000000000 : ℝ)*X 2 1+(2858543187/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329061_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-887469089/5000000000 : ℝ)*X 0 0+(4134774719/10000000000 : ℝ)*X 0 1+(235622201/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329061_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((883017983/2000000000 : ℝ)*X 1 0+(-35751191/250000000 : ℝ)*X 1 1+(2946372557/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329061_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4447236367/10000000000 : ℝ)*X 2 0+(1629379223/2500000000 : ℝ)*X 2 1+(-14523517/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329061_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((1335306007/2000000000 : ℝ)*X 0 0+(2821919429/10000000000 : ℝ)*X 0 1+(90027519/400000000 : ℝ)*X 0 2+(1335306007/2000000000 : ℝ)*X 1 0+(2821919429/10000000000 : ℝ)*X 1 1+(90027519/400000000 : ℝ)*X 1 2+(1335306007/2000000000 : ℝ)*X 2 0+(2821919429/10000000000 : ℝ)*X 2 1+(90027519/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329061_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-576326149/5000000000 : ℝ)*X 0 0+(2315604951/5000000000 : ℝ)*X 0 1+(5891812381/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329061_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((4364274183/10000000000 : ℝ)*X 1 0+(-372968759/2500000000 : ℝ)*X 1 1+(1473501463/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329061_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((1308238763/2500000000 : ℝ)*X 2 0+(721206077/1250000000 : ℝ)*X 2 1+(-231747801/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329061_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((1853765349/2500000000 : ℝ)*X 0 0+(1903893491/10000000000 : ℝ)*X 0 1+(2246357663/10000000000 : ℝ)*X 0 2+(1853765349/2500000000 : ℝ)*X 1 0+(1903893491/10000000000 : ℝ)*X 1 1+(2246357663/10000000000 : ℝ)*X 1 2+(1853765349/2500000000 : ℝ)*X 2 0+(1903893491/10000000000 : ℝ)*X 2 1+(2246357663/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329061_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-118448497/1000000000 : ℝ)*X 0 0+(4773130313/10000000000 : ℝ)*X 0 1+(716606669/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c329061_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((5168974679/10000000000 : ℝ)*X 1 0+(-296694613/2500000000 : ℝ)*X 1 1+(2671952051/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c329061_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((541241557/1250000000 : ℝ)*X 2 0+(3209241323/5000000000 : ℝ)*X 2 1+(-398884657/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c329061_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((238883189/312500000 : ℝ)*X 0 0+(900702813/5000000000 : ℝ)*X 0 1+(2050325527/10000000000 : ℝ)*X 0 2+(238883189/312500000 : ℝ)*X 1 0+(900702813/5000000000 : ℝ)*X 1 1+(2050325527/10000000000 : ℝ)*X 1 2+(238883189/312500000 : ℝ)*X 2 0+(900702813/5000000000 : ℝ)*X 2 1+(2050325527/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c329061_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((5197/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5197/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1358813259146626270697844889/100843633950000000000000000000000 : ℝ) := by norm_num
    linear_combination (455948182831/250000000000 : ℝ)*(base59) + (8204485011203/1000000000000 : ℝ)*(major_s1_0) + (8204485011203/1000000000000 : ℝ)*(major_s1_1) + (8204485011203/1000000000000 : ℝ)*(major_s1_2) + (161352111/500000000000 : ℝ)*(sp_s1_0) + (43067287/500000000000 : ℝ)*(sp_s1_1) + (13653631/100000000000 : ℝ)*(sp_s1_6) + (2543767137819/200000000000 : ℝ)*(sp_s1_7) + (2543602708539/200000000000 : ℝ)*(sp_s1_8) + (2543782900307/200000000000 : ℝ)*(sp_s1_9) + (3689660460939/1000000000000 : ℝ)*(sp_s1_13) + (10140351/1000000000000 : ℝ)*(sp_s1_14) + (1068856399/1000000000000 : ℝ)*(sp_s1_15) + (127016067/500000000000 : ℝ)*(sp_s1_23) + (3689796997249/1000000000000 : ℝ)*(f.failure) + (3179792133417/250000000000 : ℝ)*(f.sum) + (56637623616853/477201600000000000000000000 : ℝ)*base62 + (3215088904149/6681250000000000000000000 : ℝ)*base65 + (11169914939197/27900000000000000000000000 : ℝ)*base67 + (69303910269287/213800000000000000000000000 : ℝ)*base69 + (75871418570213197/2168680300000000000000000000000 : ℝ)*base71 + (21322185723671/50717500000000000000000000 : ℝ)*base73 + (2932733300041/27900000000000000000000000 : ℝ)*base74 + (416228118279919/2028700000000000000000000000 : ℝ)*base76 + (6200404897101289/566007300000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (339/25000000000000000 : ℝ)*base86 + (339/25000000000000000 : ℝ)*base88 + (339/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27251/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(27251/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4450619498437257/1250000000000000000000 : ℝ) := by norm_num
    linear_combination (123689/50000000000 : ℝ)*(base13) + (139097/500000000000 : ℝ)*(base21) + (147459/125000000000 : ℝ)*(base40) + (233299297937/200000000000 : ℝ)*(base59) + (1542195374429/200000000000 : ℝ)*(major_s1_0) + (1542195374429/200000000000 : ℝ)*(major_s1_1) + (1542195374429/200000000000 : ℝ)*(major_s1_2) + (42020953/1000000000000 : ℝ)*(sp_s1_1) + (6965819/1000000000000 : ℝ)*(sp_s1_7) + (11954091172263/1000000000000 : ℝ)*(sp_s1_14) + (11954058590909/1000000000000 : ℝ)*(sp_s1_15) + (2988525083417/250000000000 : ℝ)*(sp_s1_16) + (3467746086083/1000000000000 : ℝ)*(sp_s1_20) + (105859511/1000000000000 : ℝ)*(sp_s1_27) + (1733925972797/500000000000 : ℝ)*(f.failure) + (5977050305931/500000000000 : ℝ)*(f.sum) + (154724369670702659/961561224000000000000000000000 : ℝ)*base63 + (3318850613683/17371250000000000000000000 : ℝ)*base64 + (55901449814921/172980000000000000000000000 : ℝ)*base66 + (149121692176423/555880000000000000000000000 : ℝ)*base68 + (813647840849620409/5638568780000000000000000000000 : ℝ)*base71 + (69802655809/253587500000000000000000 : ℝ)*base72 + (86159167180609/172980000000000000000000000 : ℝ)*base74 + (13231685590753/81148000000000000000000000 : ℝ)*base76 + (290748285415537507/3509245260000000000000000000000 : ℝ)*base79 + (67/12500000000000000 : ℝ)*base86 + (67/12500000000000000 : ℝ)*base88 + (67/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12387/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12387/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (24795978208544467262819064823/5418664597580000000000000000000000 : ℝ) := by norm_num
    linear_combination (2768407/1000000000000 : ℝ)*(base11) + (290559/500000000000 : ℝ)*(base15) + (224486627761/500000000000 : ℝ)*(base40) + (250596836083/200000000000 : ℝ)*(base59) + (1480848083573/200000000000 : ℝ)*(major_s1_0) + (1480848083573/200000000000 : ℝ)*(major_s1_1) + (1480848083573/200000000000 : ℝ)*(major_s1_2) + (21977883/1000000000000 : ℝ)*(sp_s1_0) + (17033851/500000000000 : ℝ)*(sp_s1_2) + (4648287/100000000000 : ℝ)*(sp_s1_9) + (1147855097801/100000000000 : ℝ)*(sp_s1_21) + (5739287571591/500000000000 : ℝ)*(sp_s1_22) + (358702974179/31250000000 : ℝ)*(sp_s1_23) + (3329903586081/1000000000000 : ℝ)*(sp_s1_27) + (3329903586081/1000000000000 : ℝ)*(f.failure) + (114785757243/10000000000 : ℝ)*(f.sum) + (345189343454458393/961561224000000000000000000000 : ℝ)*base62 + (73729807061/173712500000000000000000 : ℝ)*base64 + (71081407245089/172980000000000000000000000 : ℝ)*base66 + (397649484737127/555880000000000000000000000 : ℝ)*base68 + (254274303905709473/1127713756000000000000000000000 : ℝ)*base71 + (70022842082341/101435000000000000000000000 : ℝ)*base72 + (22663117353521/34596000000000000000000000 : ℝ)*base74 + (44034773732019/405740000000000000000000000 : ℝ)*base76 + (1447276261787238899/3509245260000000000000000000000 : ℝ)*base78 + (31709/25000000000000000 : ℝ)*base87 + (31709/25000000000000000 : ℝ)*base89 + (31709/25000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (93/16 : ℝ) ≤ p) (hpb : p ≤ (95/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (55589/25000 : ℝ) (160257/100000 : ℝ) (10347/12500 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev0 : (0 : ℝ) ≤ ((60861/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(60861/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(60543/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(60543/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13897/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(13897/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((5197/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5197/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27251/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(27251/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12387/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(12387/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c329061_s1 p hpa hpb X hX hprev0

#print axioms solution
