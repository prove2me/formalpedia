-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c308045_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:34:20.668134+00:00
-- url     : https://prove2.me/submissions/f039db7f-ae10-4df1-ab68-c2bc28d59e8b

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
theorem collision_support_c308045_s2_s2_1 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5665260633/10000000000 : ℝ)*x 0 + (1710338581/5000000000 : ℝ)*x 1 + (1833118591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5665260633/10000000000 : ℝ)^35 ≤ (47874016302603/100000000000000 : ℝ)^27 := by
    have hnat : (5665260633 : ℕ)^35*100000000000000^27 ≤ 47874016302603^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5665260633 10000000000 47874016302603 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1710338581/5000000000 : ℝ)^35 ≤ (24892655302411/100000000000000 : ℝ)^27 := by
    have hnat : (1710338581 : ℕ)^35*100000000000000^27 ≤ 24892655302411^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1710338581 5000000000 24892655302411 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1833118591/5000000000 : ℝ)^35 ≤ (27233328379513/100000000000000 : ℝ)^27 := by
    have hnat : (1833118591 : ℕ)^35*100000000000000^27 ≤ 27233328379513^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1833118591 5000000000 27233328379513 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5665260633/10000000000 : ℝ), (1710338581/5000000000 : ℝ), (1833118591/5000000000 : ℝ)] ![(47874016302603/100000000000000 : ℝ), (24892655302411/100000000000000 : ℝ), (27233328379513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5665260633/10000000000 : ℝ)|^35 ≤ (47874016302603/100000000000000 : ℝ)^27
        have hw : |(5665260633/10000000000 : ℝ)|=(5665260633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1710338581/5000000000 : ℝ)|^35 ≤ (24892655302411/100000000000000 : ℝ)^27
        have hw : |(1710338581/5000000000 : ℝ)|=(1710338581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1833118591/5000000000 : ℝ)|^35 ≤ (27233328379513/100000000000000 : ℝ)^27
        have hw : |(1833118591/5000000000 : ℝ)|=(1833118591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308045_s2_s2_6 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5299757431/10000000000 : ℝ)*x 0 + (-914984083/2500000000 : ℝ)*x 1 + (76800311/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5299757431/10000000000 : ℝ)^35 ≤ (43909052360087/100000000000000 : ℝ)^27 := by
    have hnat : (5299757431 : ℕ)^35*100000000000000^27 ≤ 43909052360087^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5299757431 10000000000 43909052360087 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (914984083/2500000000 : ℝ)^35 ≤ (339658406167/1250000000000 : ℝ)^27 := by
    have hnat : (914984083 : ℕ)^35*1250000000000^27 ≤ 339658406167^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      914984083 2500000000 339658406167 1250000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (76800311/200000000 : ℝ)^35 ≤ (14459137568399/50000000000000 : ℝ)^27 := by
    have hnat : (76800311 : ℕ)^35*50000000000000^27 ≤ 14459137568399^27*200000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76800311 200000000 14459137568399 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5299757431/10000000000 : ℝ), (-914984083/2500000000 : ℝ), (76800311/200000000 : ℝ)] ![(43909052360087/100000000000000 : ℝ), (339658406167/1250000000000 : ℝ), (14459137568399/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5299757431/10000000000 : ℝ)|^35 ≤ (43909052360087/100000000000000 : ℝ)^27
        have hw : |(5299757431/10000000000 : ℝ)|=(5299757431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-914984083/2500000000 : ℝ)|^35 ≤ (339658406167/1250000000000 : ℝ)^27
        have hw : |(-914984083/2500000000 : ℝ)|=(914984083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(76800311/200000000 : ℝ)|^35 ≤ (14459137568399/50000000000000 : ℝ)^27
        have hw : |(76800311/200000000 : ℝ)|=(76800311/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308045_s2_s2_7 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-40537307/1000000000 : ℝ)*x 0 + (-1822138501/2500000000 : ℝ)*x 1 + (4158656101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (40537307/1000000000 : ℝ)^35 ≤ (784038627069/50000000000000 : ℝ)^27 := by
    have hnat : (40537307 : ℕ)^35*50000000000000^27 ≤ 784038627069^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40537307 1000000000 784038627069 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1822138501/2500000000 : ℝ)^35 ≤ (33182761744909/50000000000000 : ℝ)^27 := by
    have hnat : (1822138501 : ℕ)^35*50000000000000^27 ≤ 33182761744909^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1822138501 2500000000 33182761744909 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4158656101/10000000000 : ℝ)^35 ≤ (16033199624239/50000000000000 : ℝ)^27 := by
    have hnat : (4158656101 : ℕ)^35*50000000000000^27 ≤ 16033199624239^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4158656101 10000000000 16033199624239 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-40537307/1000000000 : ℝ), (-1822138501/2500000000 : ℝ), (4158656101/10000000000 : ℝ)] ![(784038627069/50000000000000 : ℝ), (33182761744909/50000000000000 : ℝ), (16033199624239/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-40537307/1000000000 : ℝ)|^35 ≤ (784038627069/50000000000000 : ℝ)^27
        have hw : |(-40537307/1000000000 : ℝ)|=(40537307/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1822138501/2500000000 : ℝ)|^35 ≤ (33182761744909/50000000000000 : ℝ)^27
        have hw : |(-1822138501/2500000000 : ℝ)|=(1822138501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4158656101/10000000000 : ℝ)|^35 ≤ (16033199624239/50000000000000 : ℝ)^27
        have hw : |(4158656101/10000000000 : ℝ)|=(4158656101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308045_s2_s2_8 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4918282593/10000000000 : ℝ)*x 0 + (457403957/1250000000 : ℝ)*x 1 + (2124763981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4918282593/10000000000 : ℝ)^35 ≤ (39856481220491/100000000000000 : ℝ)^27 := by
    have hnat : (4918282593 : ℕ)^35*100000000000000^27 ≤ 39856481220491^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4918282593 10000000000 39856481220491 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (457403957/1250000000 : ℝ)^35 ≤ (5433178153607/20000000000000 : ℝ)^27 := by
    have hnat : (457403957 : ℕ)^35*20000000000000^27 ≤ 5433178153607^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      457403957 1250000000 5433178153607 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124763981/5000000000 : ℝ)^35 ≤ (32977627992023/100000000000000 : ℝ)^27 := by
    have hnat : (2124763981 : ℕ)^35*100000000000000^27 ≤ 32977627992023^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124763981 5000000000 32977627992023 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4918282593/10000000000 : ℝ), (457403957/1250000000 : ℝ), (2124763981/5000000000 : ℝ)] ![(39856481220491/100000000000000 : ℝ), (5433178153607/20000000000000 : ℝ), (32977627992023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4918282593/10000000000 : ℝ)|^35 ≤ (39856481220491/100000000000000 : ℝ)^27
        have hw : |(4918282593/10000000000 : ℝ)|=(4918282593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(457403957/1250000000 : ℝ)|^35 ≤ (5433178153607/20000000000000 : ℝ)^27
        have hw : |(457403957/1250000000 : ℝ)|=(457403957/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2124763981/5000000000 : ℝ)|^35 ≤ (32977627992023/100000000000000 : ℝ)^27
        have hw : |(2124763981/5000000000 : ℝ)|=(2124763981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308045_s2_s2_9 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2892127879/5000000000 : ℝ)*x 0 + (-774063079/2500000000 : ℝ)*x 1 + (-768492853/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2892127879/5000000000 : ℝ)^35 ≤ (49181559843033/100000000000000 : ℝ)^27 := by
    have hnat : (2892127879 : ℕ)^35*100000000000000^27 ≤ 49181559843033^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2892127879 5000000000 49181559843033 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (774063079/2500000000 : ℝ)^35 ≤ (21876258124227/100000000000000 : ℝ)^27 := by
    have hnat : (774063079 : ℕ)^35*100000000000000^27 ≤ 21876258124227^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      774063079 2500000000 21876258124227 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (768492853/2000000000 : ℝ)^35 ≤ (7235545504791/25000000000000 : ℝ)^27 := by
    have hnat : (768492853 : ℕ)^35*25000000000000^27 ≤ 7235545504791^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      768492853 2000000000 7235545504791 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2892127879/5000000000 : ℝ), (-774063079/2500000000 : ℝ), (-768492853/2000000000 : ℝ)] ![(49181559843033/100000000000000 : ℝ), (21876258124227/100000000000000 : ℝ), (7235545504791/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2892127879/5000000000 : ℝ)|^35 ≤ (49181559843033/100000000000000 : ℝ)^27
        have hw : |(2892127879/5000000000 : ℝ)|=(2892127879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-774063079/2500000000 : ℝ)|^35 ≤ (21876258124227/100000000000000 : ℝ)^27
        have hw : |(-774063079/2500000000 : ℝ)|=(774063079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-768492853/2000000000 : ℝ)|^35 ≤ (7235545504791/25000000000000 : ℝ)^27
        have hw : |(-768492853/2000000000 : ℝ)|=(768492853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308045_s2_s2_13 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5822141753/10000000000 : ℝ)*x 0 + (-342283649/2500000000 : ℝ)*x 1 + (2598310171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5822141753/10000000000 : ℝ)^35 ≤ (12399885647613/25000000000000 : ℝ)^27 := by
    have hnat : (5822141753 : ℕ)^35*25000000000000^27 ≤ 12399885647613^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5822141753 10000000000 12399885647613 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (342283649/2500000000 : ℝ)^35 ≤ (7595884205349/100000000000000 : ℝ)^27 := by
    have hnat : (342283649 : ℕ)^35*100000000000000^27 ≤ 7595884205349^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342283649 2500000000 7595884205349 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2598310171/5000000000 : ℝ)^35 ≤ (42804573185007/100000000000000 : ℝ)^27 := by
    have hnat : (2598310171 : ℕ)^35*100000000000000^27 ≤ 42804573185007^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598310171 5000000000 42804573185007 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5822141753/10000000000 : ℝ), (-342283649/2500000000 : ℝ), (2598310171/5000000000 : ℝ)] ![(12399885647613/25000000000000 : ℝ), (7595884205349/100000000000000 : ℝ), (42804573185007/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5822141753/10000000000 : ℝ)|^35 ≤ (12399885647613/25000000000000 : ℝ)^27
        have hw : |(5822141753/10000000000 : ℝ)|=(5822141753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-342283649/2500000000 : ℝ)|^35 ≤ (7595884205349/100000000000000 : ℝ)^27
        have hw : |(-342283649/2500000000 : ℝ)|=(342283649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2598310171/5000000000 : ℝ)|^35 ≤ (42804573185007/100000000000000 : ℝ)^27
        have hw : |(2598310171/5000000000 : ℝ)|=(2598310171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308045_s2_s2_14 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1277857/10000000000 : ℝ)*x 0 + (-571594517/1000000000 : ℝ)*x 1 + (2999848631/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1277857/10000000000 : ℝ)^35 ≤ (897113453/100000000000000 : ℝ)^27 := by
    have hnat : (1277857 : ℕ)^35*100000000000000^27 ≤ 897113453^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1277857 10000000000 897113453 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (571594517/1000000000 : ℝ)^35 ≤ (6053745473457/12500000000000 : ℝ)^27 := by
    have hnat : (571594517 : ℕ)^35*12500000000000^27 ≤ 6053745473457^27*1000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571594517 1000000000 6053745473457 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2999848631/5000000000 : ℝ)^35 ≤ (51569139086053/100000000000000 : ℝ)^27 := by
    have hnat : (2999848631 : ℕ)^35*100000000000000^27 ≤ 51569139086053^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2999848631 5000000000 51569139086053 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1277857/10000000000 : ℝ), (-571594517/1000000000 : ℝ), (2999848631/5000000000 : ℝ)] ![(897113453/100000000000000 : ℝ), (6053745473457/12500000000000 : ℝ), (51569139086053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1277857/10000000000 : ℝ)|^35 ≤ (897113453/100000000000000 : ℝ)^27
        have hw : |(-1277857/10000000000 : ℝ)|=(1277857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-571594517/1000000000 : ℝ)|^35 ≤ (6053745473457/12500000000000 : ℝ)^27
        have hw : |(-571594517/1000000000 : ℝ)|=(571594517/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2999848631/5000000000 : ℝ)|^35 ≤ (51569139086053/100000000000000 : ℝ)^27
        have hw : |(2999848631/5000000000 : ℝ)|=(2999848631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308045_s2_s2_15 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5531897961/10000000000 : ℝ)*x 0 + (688196871/2000000000 : ℝ)*x 1 + (3796826841/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5531897961/10000000000 : ℝ)^35 ≤ (46418246110513/100000000000000 : ℝ)^27 := by
    have hnat : (5531897961 : ℕ)^35*100000000000000^27 ≤ 46418246110513^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5531897961 10000000000 46418246110513 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (688196871/2000000000 : ℝ)^35 ≤ (2508438729081/10000000000000 : ℝ)^27 := by
    have hnat : (688196871 : ℕ)^35*10000000000000^27 ≤ 2508438729081^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      688196871 2000000000 2508438729081 10000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3796826841/10000000000 : ℝ)^35 ≤ (3562170823343/12500000000000 : ℝ)^27 := by
    have hnat : (3796826841 : ℕ)^35*12500000000000^27 ≤ 3562170823343^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3796826841 10000000000 3562170823343 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5531897961/10000000000 : ℝ), (688196871/2000000000 : ℝ), (3796826841/10000000000 : ℝ)] ![(46418246110513/100000000000000 : ℝ), (2508438729081/10000000000000 : ℝ), (3562170823343/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5531897961/10000000000 : ℝ)|^35 ≤ (46418246110513/100000000000000 : ℝ)^27
        have hw : |(5531897961/10000000000 : ℝ)|=(5531897961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(688196871/2000000000 : ℝ)|^35 ≤ (2508438729081/10000000000000 : ℝ)^27
        have hw : |(688196871/2000000000 : ℝ)|=(688196871/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3796826841/10000000000 : ℝ)|^35 ≤ (3562170823343/12500000000000 : ℝ)^27
        have hw : |(3796826841/10000000000 : ℝ)|=(3796826841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308045_s2_s2_16 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6565332367/10000000000 : ℝ)*x 0 + (-570766387/2000000000 : ℝ)*x 1 + (-98404851/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6565332367/10000000000 : ℝ)^35 ≤ (579576221243/1000000000000 : ℝ)^27 := by
    have hnat : (6565332367 : ℕ)^35*1000000000000^27 ≤ 579576221243^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6565332367 10000000000 579576221243 1000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (570766387/2000000000 : ℝ)^35 ≤ (4920552298417/25000000000000 : ℝ)^27 := by
    have hnat : (570766387 : ℕ)^35*25000000000000^27 ≤ 4920552298417^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      570766387 2000000000 4920552298417 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (98404851/312500000 : ℝ)^35 ≤ (5590042163993/25000000000000 : ℝ)^27 := by
    have hnat : (98404851 : ℕ)^35*25000000000000^27 ≤ 5590042163993^27*312500000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      98404851 312500000 5590042163993 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6565332367/10000000000 : ℝ), (-570766387/2000000000 : ℝ), (-98404851/312500000 : ℝ)] ![(579576221243/1000000000000 : ℝ), (4920552298417/25000000000000 : ℝ), (5590042163993/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6565332367/10000000000 : ℝ)|^35 ≤ (579576221243/1000000000000 : ℝ)^27
        have hw : |(6565332367/10000000000 : ℝ)|=(6565332367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-570766387/2000000000 : ℝ)|^35 ≤ (4920552298417/25000000000000 : ℝ)^27
        have hw : |(-570766387/2000000000 : ℝ)|=(570766387/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-98404851/312500000 : ℝ)|^35 ≤ (5590042163993/25000000000000 : ℝ)^27
        have hw : |(-98404851/312500000 : ℝ)|=(98404851/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308045_s2_s2_20 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1104264509/2000000000 : ℝ)*x 0 + (-1769030223/5000000000 : ℝ)*x 1 + (74273951/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1104264509/2000000000 : ℝ)^35 ≤ (144697647907/312500000000 : ℝ)^27 := by
    have hnat : (1104264509 : ℕ)^35*312500000000^27 ≤ 144697647907^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104264509 2000000000 144697647907 312500000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1769030223/5000000000 : ℝ)^35 ≤ (26005551162839/100000000000000 : ℝ)^27 := by
    have hnat : (1769030223 : ℕ)^35*100000000000000^27 ≤ 26005551162839^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769030223 5000000000 26005551162839 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (74273951/200000000 : ℝ)^35 ≤ (27691201485519/100000000000000 : ℝ)^27 := by
    have hnat : (74273951 : ℕ)^35*100000000000000^27 ≤ 27691201485519^27*200000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74273951 200000000 27691201485519 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1104264509/2000000000 : ℝ), (-1769030223/5000000000 : ℝ), (74273951/200000000 : ℝ)] ![(144697647907/312500000000 : ℝ), (26005551162839/100000000000000 : ℝ), (27691201485519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1104264509/2000000000 : ℝ)|^35 ≤ (144697647907/312500000000 : ℝ)^27
        have hw : |(1104264509/2000000000 : ℝ)|=(1104264509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1769030223/5000000000 : ℝ)|^35 ≤ (26005551162839/100000000000000 : ℝ)^27
        have hw : |(-1769030223/5000000000 : ℝ)|=(1769030223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(74273951/200000000 : ℝ)|^35 ≤ (27691201485519/100000000000000 : ℝ)^27
        have hw : |(74273951/200000000 : ℝ)|=(74273951/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308045_s2_s2_21 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-235653/625000000 : ℝ)*x 0 + (-265859151/400000000 : ℝ)*x 1 + (1007407817/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (235653/625000000 : ℝ)^35 ≤ (455932847/12500000000000 : ℝ)^27 := by
    have hnat : (235653 : ℕ)^35*12500000000000^27 ≤ 455932847^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235653 625000000 455932847 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (265859151/400000000 : ℝ)^35 ≤ (29443957437449/50000000000000 : ℝ)^27 := by
    have hnat : (265859151 : ℕ)^35*50000000000000^27 ≤ 29443957437449^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265859151 400000000 29443957437449 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1007407817/2000000000 : ℝ)^35 ≤ (10277109410373/25000000000000 : ℝ)^27 := by
    have hnat : (1007407817 : ℕ)^35*25000000000000^27 ≤ 10277109410373^27*2000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007407817 2000000000 10277109410373 25000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-235653/625000000 : ℝ), (-265859151/400000000 : ℝ), (1007407817/2000000000 : ℝ)] ![(455932847/12500000000000 : ℝ), (29443957437449/50000000000000 : ℝ), (10277109410373/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-235653/625000000 : ℝ)|^35 ≤ (455932847/12500000000000 : ℝ)^27
        have hw : |(-235653/625000000 : ℝ)|=(235653/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-265859151/400000000 : ℝ)|^35 ≤ (29443957437449/50000000000000 : ℝ)^27
        have hw : |(-265859151/400000000 : ℝ)|=(265859151/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1007407817/2000000000 : ℝ)|^35 ≤ (10277109410373/25000000000000 : ℝ)^27
        have hw : |(1007407817/2000000000 : ℝ)|=(1007407817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308045_s2_s2_22 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3259542831/5000000000 : ℝ)*x 0 + (1512450059/5000000000 : ℝ)*x 1 + (189887511/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3259542831/5000000000 : ℝ)^35 ≤ (28714476033407/50000000000000 : ℝ)^27 := by
    have hnat : (3259542831 : ℕ)^35*50000000000000^27 ≤ 28714476033407^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3259542831 5000000000 28714476033407 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1512450059/5000000000 : ℝ)^35 ≤ (21224997265019/100000000000000 : ℝ)^27 := by
    have hnat : (1512450059 : ℕ)^35*100000000000000^27 ≤ 21224997265019^27*5000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1512450059 5000000000 21224997265019 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (189887511/625000000 : ℝ)^35 ≤ (2668256330957/12500000000000 : ℝ)^27 := by
    have hnat : (189887511 : ℕ)^35*12500000000000^27 ≤ 2668256330957^27*625000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189887511 625000000 2668256330957 12500000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3259542831/5000000000 : ℝ), (1512450059/5000000000 : ℝ), (189887511/625000000 : ℝ)] ![(28714476033407/50000000000000 : ℝ), (21224997265019/100000000000000 : ℝ), (2668256330957/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3259542831/5000000000 : ℝ)|^35 ≤ (28714476033407/50000000000000 : ℝ)^27
        have hw : |(3259542831/5000000000 : ℝ)|=(3259542831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1512450059/5000000000 : ℝ)|^35 ≤ (21224997265019/100000000000000 : ℝ)^27
        have hw : |(1512450059/5000000000 : ℝ)|=(1512450059/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(189887511/625000000 : ℝ)|^35 ≤ (2668256330957/12500000000000 : ℝ)^27
        have hw : |(189887511/625000000 : ℝ)|=(189887511/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308045_s2_s2_23 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5317851153/10000000000 : ℝ)*x 0 + (-466322881/1250000000 : ℝ)*x 1 + (-937484469/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5317851153/10000000000 : ℝ)^35 ≤ (8820695256003/20000000000000 : ℝ)^27 := by
    have hnat : (5317851153 : ℕ)^35*20000000000000^27 ≤ 8820695256003^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5317851153 10000000000 8820695256003 20000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (466322881/1250000000 : ℝ)^35 ≤ (27854523810787/100000000000000 : ℝ)^27 := by
    have hnat : (466322881 : ℕ)^35*100000000000000^27 ≤ 27854523810787^27*1250000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466322881 1250000000 27854523810787 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (937484469/2500000000 : ℝ)^35 ≤ (1402099995191/5000000000000 : ℝ)^27 := by
    have hnat : (937484469 : ℕ)^35*5000000000000^27 ≤ 1402099995191^27*2500000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937484469 2500000000 1402099995191 5000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5317851153/10000000000 : ℝ), (-466322881/1250000000 : ℝ), (-937484469/2500000000 : ℝ)] ![(8820695256003/20000000000000 : ℝ), (27854523810787/100000000000000 : ℝ), (1402099995191/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5317851153/10000000000 : ℝ)|^35 ≤ (8820695256003/20000000000000 : ℝ)^27
        have hw : |(5317851153/10000000000 : ℝ)|=(5317851153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-466322881/1250000000 : ℝ)|^35 ≤ (27854523810787/100000000000000 : ℝ)^27
        have hw : |(-466322881/1250000000 : ℝ)|=(466322881/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-937484469/2500000000 : ℝ)|^35 ≤ (1402099995191/5000000000000 : ℝ)^27
        have hw : |(-937484469/2500000000 : ℝ)|=(937484469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c308045_s2_s2_27 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6071525521/10000000000 : ℝ)*x 0 + (-109578601/400000000 : ℝ)*x 1 + (3844623161/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6071525521/10000000000 : ℝ)^35 ≤ (52370868117431/100000000000000 : ℝ)^27 := by
    have hnat : (6071525521 : ℕ)^35*100000000000000^27 ≤ 52370868117431^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6071525521 10000000000 52370868117431 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109578601/400000000 : ℝ)^35 ≤ (9332934371453/50000000000000 : ℝ)^27 := by
    have hnat : (109578601 : ℕ)^35*50000000000000^27 ≤ 9332934371453^27*400000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109578601 400000000 9332934371453 50000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3844623161/10000000000 : ℝ)^35 ≤ (28963263134211/100000000000000 : ℝ)^27 := by
    have hnat : (3844623161 : ℕ)^35*100000000000000^27 ≤ 28963263134211^27*10000000000^35 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3844623161 10000000000 28963263134211 100000000000000 35 27 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (35/8 : ℝ)) 35 27 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6071525521/10000000000 : ℝ), (-109578601/400000000 : ℝ), (3844623161/10000000000 : ℝ)] ![(52370868117431/100000000000000 : ℝ), (9332934371453/50000000000000 : ℝ), (28963263134211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6071525521/10000000000 : ℝ)|^35 ≤ (52370868117431/100000000000000 : ℝ)^27
        have hw : |(6071525521/10000000000 : ℝ)|=(6071525521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-109578601/400000000 : ℝ)|^35 ≤ (9332934371453/50000000000000 : ℝ)^27
        have hw : |(-109578601/400000000 : ℝ)|=(109578601/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3844623161/10000000000 : ℝ)|^35 ≤ (28963263134211/100000000000000 : ℝ)^27
        have hw : |(3844623161/10000000000 : ℝ)|=(3844623161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c308045_s2 (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((12563/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12563/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-13477/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-13477/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15947/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15947/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2049/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2049/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-37349/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-37349/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10239/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(10239/25000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (3861/5000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base22 : ((-1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).1]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (12563/25000 : ℝ) ^ (17/4 : ℝ) ≤ (83892235669531749/1562500000000000000 : ℝ) := by
    have hpowers : (12563/25000 : ℝ)^17 ≤ (83892235669531749/1562500000000000000 : ℝ)^4 := by
      have hnat : (12563 : ℕ)^17*1562500000000000000^4 ≤ 83892235669531749^4*25000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12563 25000 83892235669531749 1562500000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12563/25000 : ℝ)) (X := (83892235669531749/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner0a : (1646392235669531749/1562500000000000000 : ℝ) ≤ (5061908683935403/5000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (1646392235669531749/1562500000000000000 : ℝ)^4 ≤ (5061908683935403/5000000000000000 : ℝ)^17 := by
      have hnat : (1646392235669531749 : ℕ)^4*5000000000000000^17 ≤ 5061908683935403^17*1562500000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1646392235669531749 1562500000000000000 5061908683935403 5000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5061908683935403/5000000000000000 : ℝ)) (X := (1646392235669531749/1562500000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner0b : (865142235669531749/781250000000000000 : ℝ) ≤ (2048580022008967/2000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (865142235669531749/781250000000000000 : ℝ)^4 ≤ (2048580022008967/2000000000000000 : ℝ)^17 := by
      have hnat : (865142235669531749 : ℕ)^4*2000000000000000^17 ≤ 2048580022008967^17*781250000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        865142235669531749 781250000000000000 2048580022008967 2000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2048580022008967/2000000000000000 : ℝ)) (X := (865142235669531749/781250000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(61908683935403/2512600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(119082742174029/5025200000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (12563/25000 : ℝ)) (alpha := (61908683935403/2512600000000000 : ℝ)) (beta := (119082742174029/5025200000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (12563/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(61908683935403/2512600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(119082742174029/5025200000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (13477/20000 : ℝ) ^ (17/4 : ℝ) ≤ (9340362753289688331/50000000000000000000 : ℝ) := by
    have hpowers : (13477/20000 : ℝ)^17 ≤ (9340362753289688331/50000000000000000000 : ℝ)^4 := by
      have hnat : (13477 : ℕ)^17*50000000000000000000^4 ≤ 9340362753289688331^4*20000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13477 20000 9340362753289688331 50000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13477/20000 : ℝ)) (X := (9340362753289688331/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner1a : (59340362753289688331/50000000000000000000 : ℝ) ≤ (10411210365393879/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (59340362753289688331/50000000000000000000 : ℝ)^4 ≤ (10411210365393879/10000000000000000 : ℝ)^17 := by
      have hnat : (59340362753289688331 : ℕ)^4*10000000000000000^17 ≤ 10411210365393879^17*50000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        59340362753289688331 50000000000000000000 10411210365393879 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10411210365393879/10000000000000000 : ℝ)) (X := (59340362753289688331/50000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner1b : (34340362753289688331/25000000000000000000 : ℝ) ≤ (2155106756979451/2000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (34340362753289688331/25000000000000000000 : ℝ)^4 ≤ (2155106756979451/2000000000000000 : ℝ)^17 := by
      have hnat : (34340362753289688331 : ℕ)^4*2000000000000000^17 ≤ 2155106756979451^17*25000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34340362753289688331 25000000000000000000 2155106756979451 2000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2155106756979451/2000000000000000 : ℝ)) (X := (34340362753289688331/25000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(411210365393879/6738500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(22770213718961/421156250000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (13477/20000 : ℝ)) (alpha := (411210365393879/6738500000000000 : ℝ)) (beta := (22770213718961/421156250000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (13477/20000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(411210365393879/6738500000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(22770213718961/421156250000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (15947/20000 : ℝ) ^ (17/4 : ℝ) ≤ (3819515210788395561/10000000000000000000 : ℝ) := by
    have hpowers : (15947/20000 : ℝ)^17 ≤ (3819515210788395561/10000000000000000000 : ℝ)^4 := by
      have hnat : (15947 : ℕ)^17*10000000000000000000^4 ≤ 3819515210788395561^4*20000^17 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15947 20000 3819515210788395561 10000000000000000000 17 4 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15947/20000 : ℝ)) (X := (3819515210788395561/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner2a : (13819515210788395561/10000000000000000000 : ℝ) ≤ (10790886667848389/10000000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (13819515210788395561/10000000000000000000 : ℝ)^4 ≤ (10790886667848389/10000000000000000 : ℝ)^17 := by
      have hnat : (13819515210788395561 : ℕ)^4*10000000000000000^17 ≤ 10790886667848389^17*10000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13819515210788395561 10000000000000000000 10790886667848389 10000000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10790886667848389/10000000000000000 : ℝ)) (X := (13819515210788395561/10000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have s2_corner2b : (8819515210788395561/5000000000000000000 : ℝ) ≤ (2857156687533669/2500000000000000 : ℝ) ^ (17/4 : ℝ) := by
    have hpowers : (8819515210788395561/5000000000000000000 : ℝ)^4 ≤ (2857156687533669/2500000000000000 : ℝ)^17 := by
      have hnat : (8819515210788395561 : ℕ)^4*2500000000000000^17 ≤ 2857156687533669^17*5000000000000000000^4 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8819515210788395561 5000000000000000000 2857156687533669 2500000000000000 4 17 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2857156687533669/2500000000000000 : ℝ)) (X := (8819515210788395561/5000000000000000000 : ℝ)) (by norm_num) 17 4 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(790886667848389/7973500000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(637740082286287/7973500000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (17/4 : ℝ)) (rho := (15947/20000 : ℝ)) (alpha := (790886667848389/7973500000000000 : ℝ)) (beta := (637740082286287/7973500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (15947/20000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(790886667848389/7973500000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(637740082286287/7973500000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_1 : ((5665260633/10000000000 : ℝ)*X 1 0+(1710338581/5000000000 : ℝ)*X 1 1+(1833118591/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308045_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((5299757431/10000000000 : ℝ)*X 0 0+(-914984083/2500000000 : ℝ)*X 0 1+(76800311/200000000 : ℝ)*X 0 2+(5299757431/10000000000 : ℝ)*X 1 0+(-914984083/2500000000 : ℝ)*X 1 1+(76800311/200000000 : ℝ)*X 1 2+(5299757431/10000000000 : ℝ)*X 2 0+(-914984083/2500000000 : ℝ)*X 2 1+(76800311/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308045_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-40537307/1000000000 : ℝ)*X 0 0+(-1822138501/2500000000 : ℝ)*X 0 1+(4158656101/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308045_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((4918282593/10000000000 : ℝ)*X 1 0+(457403957/1250000000 : ℝ)*X 1 1+(2124763981/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308045_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((2892127879/5000000000 : ℝ)*X 2 0+(-774063079/2500000000 : ℝ)*X 2 1+(-768492853/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308045_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((5822141753/10000000000 : ℝ)*X 0 0+(-342283649/2500000000 : ℝ)*X 0 1+(2598310171/5000000000 : ℝ)*X 0 2+(5822141753/10000000000 : ℝ)*X 1 0+(-342283649/2500000000 : ℝ)*X 1 1+(2598310171/5000000000 : ℝ)*X 1 2+(5822141753/10000000000 : ℝ)*X 2 0+(-342283649/2500000000 : ℝ)*X 2 1+(2598310171/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308045_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-1277857/10000000000 : ℝ)*X 0 0+(-571594517/1000000000 : ℝ)*X 0 1+(2999848631/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308045_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((5531897961/10000000000 : ℝ)*X 1 0+(688196871/2000000000 : ℝ)*X 1 1+(3796826841/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308045_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((6565332367/10000000000 : ℝ)*X 2 0+(-570766387/2000000000 : ℝ)*X 2 1+(-98404851/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308045_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((1104264509/2000000000 : ℝ)*X 0 0+(-1769030223/5000000000 : ℝ)*X 0 1+(74273951/200000000 : ℝ)*X 0 2+(1104264509/2000000000 : ℝ)*X 1 0+(-1769030223/5000000000 : ℝ)*X 1 1+(74273951/200000000 : ℝ)*X 1 2+(1104264509/2000000000 : ℝ)*X 2 0+(-1769030223/5000000000 : ℝ)*X 2 1+(74273951/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308045_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-235653/625000000 : ℝ)*X 0 0+(-265859151/400000000 : ℝ)*X 0 1+(1007407817/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c308045_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((3259542831/5000000000 : ℝ)*X 1 0+(1512450059/5000000000 : ℝ)*X 1 1+(189887511/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c308045_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((5317851153/10000000000 : ℝ)*X 2 0+(-466322881/1250000000 : ℝ)*X 2 1+(-937484469/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c308045_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((6071525521/10000000000 : ℝ)*X 0 0+(-109578601/400000000 : ℝ)*X 0 1+(3844623161/10000000000 : ℝ)*X 0 2+(6071525521/10000000000 : ℝ)*X 1 0+(-109578601/400000000 : ℝ)*X 1 1+(3844623161/10000000000 : ℝ)*X 1 2+(6071525521/10000000000 : ℝ)*X 2 0+(-109578601/400000000 : ℝ)*X 2 1+(3844623161/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c308045_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((2049/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2049/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (4912800426727183669400175255159/675002825949250000000000000000000000 : ℝ) := by norm_num
    linear_combination (584529/250000000000 : ℝ)*(base24) + (64231582881/200000000000 : ℝ)*(base40) + (22112837901/50000000000 : ℝ)*(base50) + (2716133/1000000000000 : ℝ)*(base60) + (354145503927/125000000000 : ℝ)*(major_s2_0) + (354145503927/125000000000 : ℝ)*(major_s2_1) + (354145503927/125000000000 : ℝ)*(major_s2_2) + (357393/50000000000 : ℝ)*(sp_s2_6) + (1929198159027/500000000000 : ℝ)*(sp_s2_7) + (1929217329101/500000000000 : ℝ)*(sp_s2_8) + (3858357976537/1000000000000 : ℝ)*(sp_s2_9) + (1807883830703/1000000000000 : ℝ)*(sp_s2_13) + (9585037/250000000000 : ℝ)*(sp_s2_21) + (74343549/1000000000000 : ℝ)*(sp_s2_23) + (1807890978563/1000000000000 : ℝ)*(f.failure) + (1929217329101/500000000000 : ℝ)*(f.sum) + (10909997957554974697/53729429750000000000000000000000 : ℝ)*base62 + (260885107870749/996687500000000000000000000 : ℝ)*base64 + (148115265707573/842312500000000000000000000 : ℝ)*base66 + (1770727201663963/3986750000000000000000000000 : ℝ)*base68 + (4666582760281692189/25042770125000000000000000000000 : ℝ)*base70 + (163751768204367/628150000000000000000000000 : ℝ)*base72 + (508698543905991/1684625000000000000000000000 : ℝ)*base75 + (84356885592021/314075000000000000000000000 : ℝ)*base77 + (446534662945334327/5290985968750000000000000000000 : ℝ)*base78 + (13707/100000000000000000 : ℝ)*base86 + (13707/100000000000000000 : ℝ)*base88 + (13707/100000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-37349/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-37349/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (7632139807130486379391428791517/1350005651898500000000000000000000000 : ℝ) := by norm_num
    linear_combination (118884883623/1000000000000 : ℝ)*(base39) + (314611522809/200000000000 : ℝ)*(base40) + (35140865979/1000000000000 : ℝ)*(base60) + (2696545075583/500000000000 : ℝ)*(major_s2_0) + (2696545075583/500000000000 : ℝ)*(major_s2_1) + (2696545075583/500000000000 : ℝ)*(major_s2_2) + (15636893/500000000000 : ℝ)*(sp_s2_1) + (44525519/1000000000000 : ℝ)*(sp_s2_6) + (6239371/250000000000 : ℝ)*(sp_s2_9) + (1836188574707/250000000000 : ℝ)*(sp_s2_14) + (7344723025043/1000000000000 : ℝ)*(sp_s2_15) + (229522791917/31250000000 : ℝ)*(sp_s2_16) + (3441296651193/1000000000000 : ℝ)*(sp_s2_20) + (41471157/500000000000 : ℝ)*(sp_s2_27) + (1720712059513/500000000000 : ℝ)*(f.failure) + (1836188574707/250000000000 : ℝ)*(f.sum) + (15011598654879064011/26864714875000000000000000000000 : ℝ)*base62 + (229967189550021/3986750000000000000000000000 : ℝ)*base64 + (457591505290021/1684625000000000000000000000 : ℝ)*base66 + (624606027262911/498343750000000000000000000 : ℝ)*base68 + (16323962616806092981/100171080500000000000000000000000 : ℝ)*base70 + (2872319145801033/2512600000000000000000000000 : ℝ)*base72 + (1043074124280443/3369250000000000000000000000 : ℝ)*base74 + (781738777651549/1256300000000000000000000000 : ℝ)*base77 + (120295683298294826989/169311551000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (41743/50000000000000000 : ℝ)*base87 + (41743/50000000000000000 : ℝ)*base89 + (41743/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10239/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(10239/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (151395612002052631768178331/12521385062500000000000000000000 : ℝ) := by norm_num
    linear_combination (66117/8000000000 : ℝ)*(base22) + (1619683/200000000000 : ℝ)*(base39) + (830615780749/500000000000 : ℝ)*(base40) + (17975844289/62500000000 : ℝ)*(base50) + (955517/500000000000 : ℝ)*(base59) + (1419908488853/250000000000 : ℝ)*(major_s2_0) + (1419908488853/250000000000 : ℝ)*(major_s2_1) + (1419908488853/250000000000 : ℝ)*(major_s2_2) + (17941223/250000000000 : ℝ)*(sp_s2_7) + (51033567/1000000000000 : ℝ)*(sp_s2_16) + (966864929781/125000000000 : ℝ)*(sp_s2_21) + (386749560157/50000000000 : ℝ)*(sp_s2_22) + (1933732976237/250000000000 : ℝ)*(sp_s2_23) + (906068169339/250000000000 : ℝ)*(sp_s2_27) + (906068169339/250000000000 : ℝ)*(f.failure) + (386749560157/50000000000 : ℝ)*(f.sum) + (6336782542170767/104940292480468750000000000000 : ℝ)*base62 + (1541872136238861/1993375000000000000000000000 : ℝ)*base64 + (16986193985477/26322265625000000000000000 : ℝ)*base67 + (986716889323667/1993375000000000000000000000 : ℝ)*base69 + (30263588831080191821/50085540250000000000000000000000 : ℝ)*base70 + (140052678276457/1256300000000000000000000000 : ℝ)*base73 + (1435862974424249/3369250000000000000000000000 : ℝ)*base75 + (109356385498403/314075000000000000000000000 : ℝ)*base76 + (9750859029794615999/84655775500000000000000000000000 : ℝ)*base78 + (15971/25000000000000000 : ℝ)*base86 + (15971/25000000000000000 : ℝ)*base88 + (15971/25000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (17/4 : ℝ) ≤ p) (hpb : p ≤ (35/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (156711/100000 : ℝ) (11517/6250 : ℝ) (3861/5000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, true], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((12563/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12563/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-13477/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-13477/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(15947/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(15947/20000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2049/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2049/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-37349/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-37349/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(10239/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(10239/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c308045_s2 p hpa hpb X hX hprev1

#print axioms solution
