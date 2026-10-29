-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c320053_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:36:06.227508+00:00
-- url     : https://prove2.me/submissions/75933246-7133-49b5-8f8f-cab168f39884

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
theorem collision_support_c320053_s2_s2_0 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2295320593/10000000000 : ℝ)*x 0 + (2483552773/5000000000 : ℝ)*x 1 + (2487960381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2295320593/10000000000 : ℝ)^41 ≤ (16065575489583/100000000000000 : ℝ)^33 := by
    have hnat : (2295320593 : ℕ)^41*100000000000000^33 ≤ 16065575489583^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2295320593 10000000000 16065575489583 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2483552773/5000000000 : ℝ)^41 ≤ (2620061586889/6250000000000 : ℝ)^33 := by
    have hnat : (2483552773 : ℕ)^41*6250000000000^33 ≤ 2620061586889^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2483552773 5000000000 2620061586889 6250000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2487960381/5000000000 : ℝ)^41 ≤ (21006719549949/50000000000000 : ℝ)^33 := by
    have hnat : (2487960381 : ℕ)^41*50000000000000^33 ≤ 21006719549949^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2487960381 5000000000 21006719549949 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2295320593/10000000000 : ℝ), (2483552773/5000000000 : ℝ), (2487960381/5000000000 : ℝ)] ![(16065575489583/100000000000000 : ℝ), (2620061586889/6250000000000 : ℝ), (21006719549949/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2295320593/10000000000 : ℝ)|^41 ≤ (16065575489583/100000000000000 : ℝ)^33
        have hw : |(-2295320593/10000000000 : ℝ)|=(2295320593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2483552773/5000000000 : ℝ)|^41 ≤ (2620061586889/6250000000000 : ℝ)^33
        have hw : |(2483552773/5000000000 : ℝ)|=(2483552773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2487960381/5000000000 : ℝ)|^41 ≤ (21006719549949/50000000000000 : ℝ)^33
        have hw : |(2487960381/5000000000 : ℝ)|=(2487960381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320053_s2_s2_2 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (445232383/1000000000 : ℝ)*x 0 + (2934685777/5000000000 : ℝ)*x 1 + (-896836919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (445232383/1000000000 : ℝ)^41 ≤ (2287050052443/6250000000000 : ℝ)^33 := by
    have hnat : (445232383 : ℕ)^41*6250000000000^33 ≤ 2287050052443^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      445232383 1000000000 2287050052443 6250000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2934685777/5000000000 : ℝ)^41 ≤ (51581337308249/100000000000000 : ℝ)^33 := by
    have hnat : (2934685777 : ℕ)^41*100000000000000^33 ≤ 51581337308249^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2934685777 5000000000 51581337308249 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (896836919/5000000000 : ℝ)^41 ≤ (11825861833557/100000000000000 : ℝ)^33 := by
    have hnat : (896836919 : ℕ)^41*100000000000000^33 ≤ 11825861833557^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896836919 5000000000 11825861833557 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(445232383/1000000000 : ℝ), (2934685777/5000000000 : ℝ), (-896836919/5000000000 : ℝ)] ![(2287050052443/6250000000000 : ℝ), (51581337308249/100000000000000 : ℝ), (11825861833557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(445232383/1000000000 : ℝ)|^41 ≤ (2287050052443/6250000000000 : ℝ)^33
        have hw : |(445232383/1000000000 : ℝ)|=(445232383/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2934685777/5000000000 : ℝ)|^41 ≤ (51581337308249/100000000000000 : ℝ)^33
        have hw : |(2934685777/5000000000 : ℝ)|=(2934685777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-896836919/5000000000 : ℝ)|^41 ≤ (11825861833557/100000000000000 : ℝ)^33
        have hw : |(-896836919/5000000000 : ℝ)|=(896836919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320053_s2_s2_6 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6700592569/10000000000 : ℝ)*x 0 + (42200437/156250000 : ℝ)*x 1 + (2685751051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6700592569/10000000000 : ℝ)^41 ≤ (6080773660903/10000000000000 : ℝ)^33 := by
    have hnat : (6700592569 : ℕ)^41*10000000000000^33 ≤ 6080773660903^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6700592569 10000000000 6080773660903 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42200437/156250000 : ℝ)^41 ≤ (19664277499809/100000000000000 : ℝ)^33 := by
    have hnat : (42200437 : ℕ)^41*100000000000000^33 ≤ 19664277499809^33*156250000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42200437 156250000 19664277499809 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2685751051/10000000000 : ℝ)^41 ≤ (19527985879669/100000000000000 : ℝ)^33 := by
    have hnat : (2685751051 : ℕ)^41*100000000000000^33 ≤ 19527985879669^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2685751051 10000000000 19527985879669 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6700592569/10000000000 : ℝ), (42200437/156250000 : ℝ), (2685751051/10000000000 : ℝ)] ![(6080773660903/10000000000000 : ℝ), (19664277499809/100000000000000 : ℝ), (19527985879669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6700592569/10000000000 : ℝ)|^41 ≤ (6080773660903/10000000000000 : ℝ)^33
        have hw : |(6700592569/10000000000 : ℝ)|=(6700592569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42200437/156250000 : ℝ)|^41 ≤ (19664277499809/100000000000000 : ℝ)^33
        have hw : |(42200437/156250000 : ℝ)|=(42200437/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2685751051/10000000000 : ℝ)|^41 ≤ (19527985879669/100000000000000 : ℝ)^33
        have hw : |(2685751051/10000000000 : ℝ)|=(2685751051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320053_s2_s2_7 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-2286389117/10000000000 : ℝ)*x 0 + (4560743759/10000000000 : ℝ)*x 1 + (672683411/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2286389117/10000000000 : ℝ)^41 ≤ (1998492931199/12500000000000 : ℝ)^33 := by
    have hnat : (2286389117 : ℕ)^41*12500000000000^33 ≤ 1998492931199^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2286389117 10000000000 1998492931199 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4560743759/10000000000 : ℝ)^41 ≤ (18851575773883/50000000000000 : ℝ)^33 := by
    have hnat : (4560743759 : ℕ)^41*50000000000000^33 ≤ 18851575773883^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4560743759 10000000000 18851575773883 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672683411/1250000000 : ℝ)^41 ≤ (46308904991581/100000000000000 : ℝ)^33 := by
    have hnat : (672683411 : ℕ)^41*100000000000000^33 ≤ 46308904991581^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672683411 1250000000 46308904991581 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2286389117/10000000000 : ℝ), (4560743759/10000000000 : ℝ), (672683411/1250000000 : ℝ)] ![(1998492931199/12500000000000 : ℝ), (18851575773883/50000000000000 : ℝ), (46308904991581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2286389117/10000000000 : ℝ)|^41 ≤ (1998492931199/12500000000000 : ℝ)^33
        have hw : |(-2286389117/10000000000 : ℝ)|=(2286389117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4560743759/10000000000 : ℝ)|^41 ≤ (18851575773883/50000000000000 : ℝ)^33
        have hw : |(4560743759/10000000000 : ℝ)|=(4560743759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(672683411/1250000000 : ℝ)|^41 ≤ (46308904991581/100000000000000 : ℝ)^33
        have hw : |(672683411/1250000000 : ℝ)|=(672683411/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320053_s2_s2_8 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4352000781/10000000000 : ℝ)*x 0 + (-833924489/5000000000 : ℝ)*x 1 + (1211160703/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352000781/10000000000 : ℝ)^41 ≤ (35571191332141/100000000000000 : ℝ)^33 := by
    have hnat : (4352000781 : ℕ)^41*100000000000000^33 ≤ 35571191332141^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352000781 10000000000 35571191332141 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (833924489/5000000000 : ℝ)^41 ≤ (10804101512577/100000000000000 : ℝ)^33 := by
    have hnat : (833924489 : ℕ)^41*100000000000000^33 ≤ 10804101512577^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      833924489 5000000000 10804101512577 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1211160703/2000000000 : ℝ)^41 ≤ (418943024603/781250000000 : ℝ)^33 := by
    have hnat : (1211160703 : ℕ)^41*781250000000^33 ≤ 418943024603^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1211160703 2000000000 418943024603 781250000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352000781/10000000000 : ℝ), (-833924489/5000000000 : ℝ), (1211160703/2000000000 : ℝ)] ![(35571191332141/100000000000000 : ℝ), (10804101512577/100000000000000 : ℝ), (418943024603/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352000781/10000000000 : ℝ)|^41 ≤ (35571191332141/100000000000000 : ℝ)^33
        have hw : |(4352000781/10000000000 : ℝ)|=(4352000781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-833924489/5000000000 : ℝ)|^41 ≤ (10804101512577/100000000000000 : ℝ)^33
        have hw : |(-833924489/5000000000 : ℝ)|=(833924489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1211160703/2000000000 : ℝ)|^41 ≤ (418943024603/781250000000 : ℝ)^33
        have hw : |(1211160703/2000000000 : ℝ)|=(1211160703/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320053_s2_s2_9 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (436422333/1000000000 : ℝ)*x 0 + (6239839713/10000000000 : ℝ)*x 1 + (-697122569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436422333/1000000000 : ℝ)^41 ≤ (35695353379093/100000000000000 : ℝ)^33 := by
    have hnat : (436422333 : ℕ)^41*100000000000000^33 ≤ 35695353379093^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436422333 1000000000 35695353379093 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6239839713/10000000000 : ℝ)^41 ≤ (55656835346611/100000000000000 : ℝ)^33 := by
    have hnat : (6239839713 : ℕ)^41*100000000000000^33 ≤ 55656835346611^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6239839713 10000000000 55656835346611 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (697122569/5000000000 : ℝ)^41 ≤ (4323905631291/50000000000000 : ℝ)^33 := by
    have hnat : (697122569 : ℕ)^41*50000000000000^33 ≤ 4323905631291^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      697122569 5000000000 4323905631291 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436422333/1000000000 : ℝ), (6239839713/10000000000 : ℝ), (-697122569/5000000000 : ℝ)] ![(35695353379093/100000000000000 : ℝ), (55656835346611/100000000000000 : ℝ), (4323905631291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436422333/1000000000 : ℝ)|^41 ≤ (35695353379093/100000000000000 : ℝ)^33
        have hw : |(436422333/1000000000 : ℝ)|=(436422333/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6239839713/10000000000 : ℝ)|^41 ≤ (55656835346611/100000000000000 : ℝ)^33
        have hw : |(6239839713/10000000000 : ℝ)|=(6239839713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-697122569/5000000000 : ℝ)|^41 ≤ (4323905631291/50000000000000 : ℝ)^33
        have hw : |(-697122569/5000000000 : ℝ)|=(697122569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320053_s2_s2_13 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3335139309/5000000000 : ℝ)*x 0 + (160047561/500000000 : ℝ)*x 1 + (2200871979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3335139309/5000000000 : ℝ)^41 ≤ (30233067622953/50000000000000 : ℝ)^33 := by
    have hnat : (3335139309 : ℕ)^41*50000000000000^33 ≤ 30233067622953^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3335139309 5000000000 30233067622953 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (160047561/500000000 : ℝ)^41 ≤ (3035685098681/12500000000000 : ℝ)^33 := by
    have hnat : (160047561 : ℕ)^41*12500000000000^33 ≤ 3035685098681^33*500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160047561 500000000 3035685098681 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2200871979/10000000000 : ℝ)^41 ≤ (7624191977/50000000000 : ℝ)^33 := by
    have hnat : (2200871979 : ℕ)^41*50000000000^33 ≤ 7624191977^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2200871979 10000000000 7624191977 50000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3335139309/5000000000 : ℝ), (160047561/500000000 : ℝ), (2200871979/10000000000 : ℝ)] ![(30233067622953/50000000000000 : ℝ), (3035685098681/12500000000000 : ℝ), (7624191977/50000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3335139309/5000000000 : ℝ)|^41 ≤ (30233067622953/50000000000000 : ℝ)^33
        have hw : |(3335139309/5000000000 : ℝ)|=(3335139309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(160047561/500000000 : ℝ)|^41 ≤ (3035685098681/12500000000000 : ℝ)^33
        have hw : |(160047561/500000000 : ℝ)|=(160047561/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2200871979/10000000000 : ℝ)|^41 ≤ (7624191977/50000000000 : ℝ)^33
        have hw : |(2200871979/10000000000 : ℝ)|=(2200871979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320053_s2_s2_14 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1912212887/10000000000 : ℝ)*x 0 + (4911780249/10000000000 : ℝ)*x 1 + (2669431163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1912212887/10000000000 : ℝ)^41 ≤ (12804517209199/100000000000000 : ℝ)^33 := by
    have hnat : (1912212887 : ℕ)^41*100000000000000^33 ≤ 12804517209199^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1912212887 10000000000 12804517209199 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4911780249/10000000000 : ℝ)^41 ≤ (20670822793399/50000000000000 : ℝ)^33 := by
    have hnat : (4911780249 : ℕ)^41*50000000000000^33 ≤ 20670822793399^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4911780249 10000000000 20670822793399 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2669431163/5000000000 : ℝ)^41 ≤ (5731729649057/12500000000000 : ℝ)^33 := by
    have hnat : (2669431163 : ℕ)^41*12500000000000^33 ≤ 5731729649057^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2669431163 5000000000 5731729649057 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1912212887/10000000000 : ℝ), (4911780249/10000000000 : ℝ), (2669431163/5000000000 : ℝ)] ![(12804517209199/100000000000000 : ℝ), (20670822793399/50000000000000 : ℝ), (5731729649057/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1912212887/10000000000 : ℝ)|^41 ≤ (12804517209199/100000000000000 : ℝ)^33
        have hw : |(-1912212887/10000000000 : ℝ)|=(1912212887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4911780249/10000000000 : ℝ)|^41 ≤ (20670822793399/50000000000000 : ℝ)^33
        have hw : |(4911780249/10000000000 : ℝ)|=(4911780249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2669431163/5000000000 : ℝ)|^41 ≤ (5731729649057/12500000000000 : ℝ)^33
        have hw : |(2669431163/5000000000 : ℝ)|=(2669431163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320053_s2_s2_15 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4273852761/10000000000 : ℝ)*x 0 + (-86610939/500000000 : ℝ)*x 1 + (1216091869/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4273852761/10000000000 : ℝ)^41 ≤ (34779334434801/100000000000000 : ℝ)^33 := by
    have hnat : (4273852761 : ℕ)^41*100000000000000^33 ≤ 34779334434801^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4273852761 10000000000 34779334434801 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (86610939/500000000 : ℝ)^41 ≤ (11324566580173/100000000000000 : ℝ)^33 := by
    have hnat : (86610939 : ℕ)^41*100000000000000^33 ≤ 11324566580173^33*500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86610939 500000000 11324566580173 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1216091869/2000000000 : ℝ)^41 ≤ (3368506185691/6250000000000 : ℝ)^33 := by
    have hnat : (1216091869 : ℕ)^41*6250000000000^33 ≤ 3368506185691^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1216091869 2000000000 3368506185691 6250000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4273852761/10000000000 : ℝ), (-86610939/500000000 : ℝ), (1216091869/2000000000 : ℝ)] ![(34779334434801/100000000000000 : ℝ), (11324566580173/100000000000000 : ℝ), (3368506185691/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4273852761/10000000000 : ℝ)|^41 ≤ (34779334434801/100000000000000 : ℝ)^33
        have hw : |(4273852761/10000000000 : ℝ)|=(4273852761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-86610939/500000000 : ℝ)|^41 ≤ (11324566580173/100000000000000 : ℝ)^33
        have hw : |(-86610939/500000000 : ℝ)|=(86610939/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1216091869/2000000000 : ℝ)|^41 ≤ (3368506185691/6250000000000 : ℝ)^33
        have hw : |(1216091869/2000000000 : ℝ)|=(1216091869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320053_s2_s2_16 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4841530911/10000000000 : ℝ)*x 0 + (28811273/50000000 : ℝ)*x 1 + (-1436849653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4841530911/10000000000 : ℝ)^41 ≤ (10152076683133/25000000000000 : ℝ)^33 := by
    have hnat : (4841530911 : ℕ)^41*25000000000000^33 ≤ 10152076683133^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4841530911 10000000000 10152076683133 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (28811273/50000000 : ℝ)^41 ≤ (25207179386319/50000000000000 : ℝ)^33 := by
    have hnat : (28811273 : ℕ)^41*50000000000000^33 ≤ 25207179386319^33*50000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28811273 50000000 25207179386319 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1436849653/10000000000 : ℝ)^41 ≤ (897733448541/10000000000000 : ℝ)^33 := by
    have hnat : (1436849653 : ℕ)^41*10000000000000^33 ≤ 897733448541^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1436849653 10000000000 897733448541 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4841530911/10000000000 : ℝ), (28811273/50000000 : ℝ), (-1436849653/10000000000 : ℝ)] ![(10152076683133/25000000000000 : ℝ), (25207179386319/50000000000000 : ℝ), (897733448541/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4841530911/10000000000 : ℝ)|^41 ≤ (10152076683133/25000000000000 : ℝ)^33
        have hw : |(4841530911/10000000000 : ℝ)|=(4841530911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(28811273/50000000 : ℝ)|^41 ≤ (25207179386319/50000000000000 : ℝ)^33
        have hw : |(28811273/50000000 : ℝ)|=(28811273/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1436849653/10000000000 : ℝ)|^41 ≤ (897733448541/10000000000000 : ℝ)^33
        have hw : |(-1436849653/10000000000 : ℝ)|=(1436849653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320053_s2_s2_20 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (7169592127/10000000000 : ℝ)*x 0 + (529748379/2000000000 : ℝ)*x 1 + (2132958363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7169592127/10000000000 : ℝ)^41 ≤ (258358548409/390625000000 : ℝ)^33 := by
    have hnat : (7169592127 : ℕ)^41*390625000000^33 ≤ 258358548409^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7169592127 10000000000 258358548409 390625000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (529748379/2000000000 : ℝ)^41 ≤ (2399277469791/12500000000000 : ℝ)^33 := by
    have hnat : (529748379 : ℕ)^41*12500000000000^33 ≤ 2399277469791^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529748379 2000000000 2399277469791 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2132958363/10000000000 : ℝ)^41 ≤ (3666497960181/25000000000000 : ℝ)^33 := by
    have hnat : (2132958363 : ℕ)^41*25000000000000^33 ≤ 3666497960181^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2132958363 10000000000 3666497960181 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7169592127/10000000000 : ℝ), (529748379/2000000000 : ℝ), (2132958363/10000000000 : ℝ)] ![(258358548409/390625000000 : ℝ), (2399277469791/12500000000000 : ℝ), (3666497960181/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7169592127/10000000000 : ℝ)|^41 ≤ (258358548409/390625000000 : ℝ)^33
        have hw : |(7169592127/10000000000 : ℝ)|=(7169592127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(529748379/2000000000 : ℝ)|^41 ≤ (2399277469791/12500000000000 : ℝ)^33
        have hw : |(529748379/2000000000 : ℝ)|=(529748379/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2132958363/10000000000 : ℝ)|^41 ≤ (3666497960181/25000000000000 : ℝ)^33
        have hw : |(2132958363/10000000000 : ℝ)|=(2132958363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320053_s2_s2_21 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-373917129/2000000000 : ℝ)*x 0 + (5125252141/10000000000 : ℝ)*x 1 + (51609913/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (373917129/2000000000 : ℝ)^41 ≤ (2490168770291/20000000000000 : ℝ)^33 := by
    have hnat : (373917129 : ℕ)^41*20000000000000^33 ≤ 2490168770291^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373917129 2000000000 2490168770291 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5125252141/10000000000 : ℝ)^41 ≤ (43585614330863/100000000000000 : ℝ)^33 := by
    have hnat : (5125252141 : ℕ)^41*100000000000000^33 ≤ 43585614330863^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5125252141 10000000000 43585614330863 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51609913/100000000 : ℝ)^41 ≤ (21981770900987/50000000000000 : ℝ)^33 := by
    have hnat : (51609913 : ℕ)^41*50000000000000^33 ≤ 21981770900987^33*100000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51609913 100000000 21981770900987 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-373917129/2000000000 : ℝ), (5125252141/10000000000 : ℝ), (51609913/100000000 : ℝ)] ![(2490168770291/20000000000000 : ℝ), (43585614330863/100000000000000 : ℝ), (21981770900987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-373917129/2000000000 : ℝ)|^41 ≤ (2490168770291/20000000000000 : ℝ)^33
        have hw : |(-373917129/2000000000 : ℝ)|=(373917129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5125252141/10000000000 : ℝ)|^41 ≤ (43585614330863/100000000000000 : ℝ)^33
        have hw : |(5125252141/10000000000 : ℝ)|=(5125252141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(51609913/100000000 : ℝ)|^41 ≤ (21981770900987/50000000000000 : ℝ)^33
        have hw : |(51609913/100000000 : ℝ)|=(51609913/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320053_s2_s2_22 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2435967189/5000000000 : ℝ)*x 0 + (-29812863/200000000 : ℝ)*x 1 + (2847200171/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2435967189/5000000000 : ℝ)^41 ≤ (40925376713471/100000000000000 : ℝ)^33 := by
    have hnat : (2435967189 : ℕ)^41*100000000000000^33 ≤ 40925376713471^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2435967189 5000000000 40925376713471 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (29812863/200000000 : ℝ)^41 ≤ (4698394027323/50000000000000 : ℝ)^33 := by
    have hnat : (29812863 : ℕ)^41*50000000000000^33 ≤ 4698394027323^33*200000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29812863 200000000 4698394027323 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2847200171/5000000000 : ℝ)^41 ≤ (24838917611071/50000000000000 : ℝ)^33 := by
    have hnat : (2847200171 : ℕ)^41*50000000000000^33 ≤ 24838917611071^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2847200171 5000000000 24838917611071 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2435967189/5000000000 : ℝ), (-29812863/200000000 : ℝ), (2847200171/5000000000 : ℝ)] ![(40925376713471/100000000000000 : ℝ), (4698394027323/50000000000000 : ℝ), (24838917611071/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2435967189/5000000000 : ℝ)|^41 ≤ (40925376713471/100000000000000 : ℝ)^33
        have hw : |(2435967189/5000000000 : ℝ)|=(2435967189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-29812863/200000000 : ℝ)|^41 ≤ (4698394027323/50000000000000 : ℝ)^33
        have hw : |(-29812863/200000000 : ℝ)|=(29812863/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2847200171/5000000000 : ℝ)|^41 ≤ (24838917611071/50000000000000 : ℝ)^33
        have hw : |(2847200171/5000000000 : ℝ)|=(2847200171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320053_s2_s2_23 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2133443819/5000000000 : ℝ)*x 0 + (3080063143/5000000000 : ℝ)*x 1 + (-13055907/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2133443819/5000000000 : ℝ)^41 ≤ (8677231909623/25000000000000 : ℝ)^33 := by
    have hnat : (2133443819 : ℕ)^41*25000000000000^33 ≤ 8677231909623^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2133443819 5000000000 8677231909623 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3080063143/5000000000 : ℝ)^41 ≤ (54774829890099/100000000000000 : ℝ)^33 := by
    have hnat : (3080063143 : ℕ)^41*100000000000000^33 ≤ 54774829890099^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3080063143 5000000000 54774829890099 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13055907/80000000 : ℝ)^41 ≤ (10516242465353/100000000000000 : ℝ)^33 := by
    have hnat : (13055907 : ℕ)^41*100000000000000^33 ≤ 10516242465353^33*80000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13055907 80000000 10516242465353 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2133443819/5000000000 : ℝ), (3080063143/5000000000 : ℝ), (-13055907/80000000 : ℝ)] ![(8677231909623/25000000000000 : ℝ), (54774829890099/100000000000000 : ℝ), (10516242465353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2133443819/5000000000 : ℝ)|^41 ≤ (8677231909623/25000000000000 : ℝ)^33
        have hw : |(2133443819/5000000000 : ℝ)|=(2133443819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3080063143/5000000000 : ℝ)|^41 ≤ (54774829890099/100000000000000 : ℝ)^33
        have hw : |(3080063143/5000000000 : ℝ)|=(3080063143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13055907/80000000 : ℝ)|^41 ≤ (10516242465353/100000000000000 : ℝ)^33
        have hw : |(-13055907/80000000 : ℝ)|=(13055907/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320053_s2_s2_27 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (112850653/156250000 : ℝ)*x 0 + (235372617/1000000000 : ℝ)*x 1 + (591397939/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (112850653/156250000 : ℝ)^41 ≤ (66746060594617/100000000000000 : ℝ)^33 := by
    have hnat : (112850653 : ℕ)^41*100000000000000^33 ≤ 66746060594617^33*156250000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112850653 156250000 66746060594617 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (235372617/1000000000 : ℝ)^41 ≤ (16575030828461/100000000000000 : ℝ)^33 := by
    have hnat : (235372617 : ℕ)^41*100000000000000^33 ≤ 16575030828461^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      235372617 1000000000 16575030828461 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (591397939/2500000000 : ℝ)^41 ≤ (16678908564597/100000000000000 : ℝ)^33 := by
    have hnat : (591397939 : ℕ)^41*100000000000000^33 ≤ 16678908564597^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      591397939 2500000000 16678908564597 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(112850653/156250000 : ℝ), (235372617/1000000000 : ℝ), (591397939/2500000000 : ℝ)] ![(66746060594617/100000000000000 : ℝ), (16575030828461/100000000000000 : ℝ), (16678908564597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(112850653/156250000 : ℝ)|^41 ≤ (66746060594617/100000000000000 : ℝ)^33
        have hw : |(112850653/156250000 : ℝ)|=(112850653/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(235372617/1000000000 : ℝ)|^41 ≤ (16575030828461/100000000000000 : ℝ)^33
        have hw : |(235372617/1000000000 : ℝ)|=(235372617/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(591397939/2500000000 : ℝ)|^41 ≤ (16678908564597/100000000000000 : ℝ)^33
        have hw : |(591397939/2500000000 : ℝ)|=(591397939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c320053_s2 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((20713/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20713/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48357/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(48357/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46191/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(46191/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1179/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1179/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5911/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5911/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2879/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2879/12500 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80273/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80273/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80273/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80273/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80273/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80273/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  have s2_pow0 : (20713/50000 : ℝ) ^ (5 : ℝ) ≤ (305003633324724139/25000000000000000000 : ℝ) := by
    have hpowers : (20713/50000 : ℝ)^5 ≤ (305003633324724139/25000000000000000000 : ℝ)^1 := by
      have hnat : (20713 : ℕ)^5*25000000000000000000^1 ≤ 305003633324724139^1*50000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20713 50000 305003633324724139 25000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20713/50000 : ℝ)) (X := (305003633324724139/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s2_corner0a : (25305003633324724139/25000000000000000000 : ℝ) ≤ (5012141040045863/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (25305003633324724139/25000000000000000000 : ℝ)^1 ≤ (5012141040045863/5000000000000000 : ℝ)^5 := by
      have hnat : (25305003633324724139 : ℕ)^1*5000000000000000^5 ≤ 5012141040045863^5*25000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25305003633324724139 25000000000000000000 5012141040045863 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5012141040045863/5000000000000000 : ℝ)) (X := (25305003633324724139/25000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s2_corner0b : (12805003633324724139/12500000000000000000 : ℝ) ≤ (502416556907707/500000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (12805003633324724139/12500000000000000000 : ℝ)^1 ≤ (502416556907707/500000000000000 : ℝ)^5 := by
      have hnat : (12805003633324724139 : ℕ)^1*500000000000000^5 ≤ 502416556907707^5*12500000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12805003633324724139 12500000000000000000 502416556907707 500000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (502416556907707/500000000000000 : ℝ)) (X := (12805003633324724139/12500000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(12141040045863/2071300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(156162714691/26900000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (20713/50000 : ℝ)) (alpha := (12141040045863/2071300000000000 : ℝ)) (beta := (156162714691/26900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (20713/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(12141040045863/2071300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(156162714691/26900000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (48357/100000 : ℝ) ^ (5 : ℝ) ≤ (2644214911659689837/100000000000000000000 : ℝ) := by
    have hpowers : (48357/100000 : ℝ)^5 ≤ (2644214911659689837/100000000000000000000 : ℝ)^1 := by
      have hnat : (48357 : ℕ)^5*100000000000000000000^1 ≤ 2644214911659689837^1*100000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48357 100000 2644214911659689837 100000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (48357/100000 : ℝ)) (X := (2644214911659689837/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s2_corner1a : (102644214911659689837/100000000000000000000 : ℝ) ≤ (10052333661654459/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (102644214911659689837/100000000000000000000 : ℝ)^1 ≤ (10052333661654459/10000000000000000 : ℝ)^5 := by
      have hnat : (102644214911659689837 : ℕ)^1*10000000000000000^5 ≤ 10052333661654459^5*100000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102644214911659689837 100000000000000000000 10052333661654459 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10052333661654459/10000000000000000 : ℝ)) (X := (102644214911659689837/100000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s2_corner1b : (52644214911659689837/50000000000000000000 : ℝ) ≤ (5051799832230231/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (52644214911659689837/50000000000000000000 : ℝ)^1 ≤ (5051799832230231/5000000000000000 : ℝ)^5 := by
      have hnat : (52644214911659689837 : ℕ)^1*5000000000000000^5 ≤ 5051799832230231^5*50000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52644214911659689837 50000000000000000000 5051799832230231 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5051799832230231/5000000000000000 : ℝ)) (X := (52644214911659689837/50000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(52333661654459/4835700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(17088667602001/1611900000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (48357/100000 : ℝ)) (alpha := (52333661654459/4835700000000000 : ℝ)) (beta := (17088667602001/1611900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (48357/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(52333661654459/4835700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(17088667602001/1611900000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (46191/100000 : ℝ) ^ (5 : ℝ) ≤ (26284325421582891/1250000000000000000 : ℝ) := by
    have hpowers : (46191/100000 : ℝ)^5 ≤ (26284325421582891/1250000000000000000 : ℝ)^1 := by
      have hnat : (46191 : ℕ)^5*1250000000000000000^1 ≤ 26284325421582891^1*100000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        46191 100000 26284325421582891 1250000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (46191/100000 : ℝ)) (X := (26284325421582891/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s2_corner2a : (1276284325421582891/1250000000000000000 : ℝ) ≤ (10041705595489487/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (1276284325421582891/1250000000000000000 : ℝ)^1 ≤ (10041705595489487/10000000000000000 : ℝ)^5 := by
      have hnat : (1276284325421582891 : ℕ)^1*10000000000000000^5 ≤ 10041705595489487^5*1250000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1276284325421582891 1250000000000000000 10041705595489487 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10041705595489487/10000000000000000 : ℝ)) (X := (1276284325421582891/1250000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s2_corner2b : (651284325421582891/625000000000000000 : ℝ) ≤ (5041364815843589/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (651284325421582891/625000000000000000 : ℝ)^1 ≤ (5041364815843589/5000000000000000 : ℝ)^5 := by
      have hnat : (651284325421582891 : ℕ)^1*5000000000000000^5 ≤ 5041364815843589^5*625000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        651284325421582891 625000000000000000 5041364815843589 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5041364815843589/5000000000000000 : ℝ)) (X := (651284325421582891/625000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(41705595489487/4619100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(41024036197691/4619100000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (46191/100000 : ℝ)) (alpha := (41705595489487/4619100000000000 : ℝ)) (beta := (41024036197691/4619100000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (46191/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(41705595489487/4619100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(41024036197691/4619100000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-2295320593/10000000000 : ℝ)*X 0 0+(2483552773/5000000000 : ℝ)*X 0 1+(2487960381/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320053_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((445232383/1000000000 : ℝ)*X 2 0+(2934685777/5000000000 : ℝ)*X 2 1+(-896836919/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320053_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((6700592569/10000000000 : ℝ)*X 0 0+(42200437/156250000 : ℝ)*X 0 1+(2685751051/10000000000 : ℝ)*X 0 2+(6700592569/10000000000 : ℝ)*X 1 0+(42200437/156250000 : ℝ)*X 1 1+(2685751051/10000000000 : ℝ)*X 1 2+(6700592569/10000000000 : ℝ)*X 2 0+(42200437/156250000 : ℝ)*X 2 1+(2685751051/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320053_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-2286389117/10000000000 : ℝ)*X 0 0+(4560743759/10000000000 : ℝ)*X 0 1+(672683411/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320053_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((4352000781/10000000000 : ℝ)*X 1 0+(-833924489/5000000000 : ℝ)*X 1 1+(1211160703/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320053_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((436422333/1000000000 : ℝ)*X 2 0+(6239839713/10000000000 : ℝ)*X 2 1+(-697122569/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320053_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((3335139309/5000000000 : ℝ)*X 0 0+(160047561/500000000 : ℝ)*X 0 1+(2200871979/10000000000 : ℝ)*X 0 2+(3335139309/5000000000 : ℝ)*X 1 0+(160047561/500000000 : ℝ)*X 1 1+(2200871979/10000000000 : ℝ)*X 1 2+(3335139309/5000000000 : ℝ)*X 2 0+(160047561/500000000 : ℝ)*X 2 1+(2200871979/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320053_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-1912212887/10000000000 : ℝ)*X 0 0+(4911780249/10000000000 : ℝ)*X 0 1+(2669431163/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320053_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((4273852761/10000000000 : ℝ)*X 1 0+(-86610939/500000000 : ℝ)*X 1 1+(1216091869/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320053_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((4841530911/10000000000 : ℝ)*X 2 0+(28811273/50000000 : ℝ)*X 2 1+(-1436849653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320053_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((7169592127/10000000000 : ℝ)*X 0 0+(529748379/2000000000 : ℝ)*X 0 1+(2132958363/10000000000 : ℝ)*X 0 2+(7169592127/10000000000 : ℝ)*X 1 0+(529748379/2000000000 : ℝ)*X 1 1+(2132958363/10000000000 : ℝ)*X 1 2+(7169592127/10000000000 : ℝ)*X 2 0+(529748379/2000000000 : ℝ)*X 2 1+(2132958363/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320053_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-373917129/2000000000 : ℝ)*X 0 0+(5125252141/10000000000 : ℝ)*X 0 1+(51609913/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320053_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((2435967189/5000000000 : ℝ)*X 1 0+(-29812863/200000000 : ℝ)*X 1 1+(2847200171/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320053_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((2133443819/5000000000 : ℝ)*X 2 0+(3080063143/5000000000 : ℝ)*X 2 1+(-13055907/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320053_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((112850653/156250000 : ℝ)*X 0 0+(235372617/1000000000 : ℝ)*X 0 1+(591397939/2500000000 : ℝ)*X 0 2+(112850653/156250000 : ℝ)*X 1 0+(235372617/1000000000 : ℝ)*X 1 1+(591397939/2500000000 : ℝ)*X 1 2+(112850653/156250000 : ℝ)*X 2 0+(235372617/1000000000 : ℝ)*X 2 1+(591397939/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320053_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((1179/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1179/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (516534227589382602287202184259/25703201126295000000000000000000000 : ℝ) := by norm_num
    linear_combination (205777926971/200000000000 : ℝ)*(base49) + (188736384329/100000000000 : ℝ)*(base59) + (269207/200000000000 : ℝ)*(base60) + (249310285019/20000000000 : ℝ)*(major_s2_0) + (249310285019/20000000000 : ℝ)*(major_s2_1) + (249310285019/20000000000 : ℝ)*(major_s2_2) + (53323697/200000000000 : ℝ)*(sp_s2_0) + (6278731/125000000000 : ℝ)*(sp_s2_6) + (18290272417317/1000000000000 : ℝ)*(sp_s2_7) + (18289878365817/1000000000000 : ℝ)*(sp_s2_8) + (18289879318753/1000000000000 : ℝ)*(sp_s2_9) + (1328086507509/200000000000 : ℝ)*(sp_s2_13) + (20645937/31250000000 : ℝ)*(sp_s2_15) + (659717049/1000000000000 : ℝ)*(sp_s2_23) + (6640482767393/1000000000000 : ℝ)*(f.failure) + (9145269517901/500000000000 : ℝ)*(f.sum) + (486324687484761523/1861381822500000000000000000000 : ℝ)*base62 + (15708382176863/115477500000000000000000000 : ℝ)*base64 + (19722536062853/80595000000000000000000000 : ℝ)*base66 + (3298088060771/14434687500000000000000000 : ℝ)*base69 + (898946394655566161/2391885457500000000000000000000 : ℝ)*base70 + (1743296699423/2690000000000000000000000 : ℝ)*base73 + (6341179249813/483570000000000000000000000 : ℝ)*base74 + (126635293293/103565000000000000000000000 : ℝ)*base76 + (6482771152058227/21680055000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (349/2500000000000000 : ℝ)*base87 + (349/2500000000000000 : ℝ)*base89 + (349/2500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5911/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5911/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3035679420999834004587224653/713977809063750000000000000000000 : ℝ) := by norm_num
    linear_combination (70863139423/62500000000 : ℝ)*(base49) + (1350243029679/1000000000000 : ℝ)*(base59) + (6134871391437/500000000000 : ℝ)*(major_s2_0) + (6134871391437/500000000000 : ℝ)*(major_s2_1) + (6134871391437/500000000000 : ℝ)*(major_s2_2) + (27745129/500000000000 : ℝ)*(sp_s2_2) + (541889/31250000000 : ℝ)*(sp_s2_6) + (6610229/250000000000 : ℝ)*(sp_s2_7) + (9802843/125000000000 : ℝ)*(sp_s2_8) + (1125204001497/62500000000 : ℝ)*(sp_s2_14) + (4500803010531/250000000000 : ℝ)*(sp_s2_15) + (1800323497461/100000000000 : ℝ)*(sp_s2_16) + (653612696549/100000000000 : ℝ)*(sp_s2_20) + (49377673/1000000000000 : ℝ)*(sp_s2_27) + (6536193683611/1000000000000 : ℝ)*(f.failure) + (18003290464867/1000000000000 : ℝ)*(f.sum) + (274900597269910237/6204606075000000000000000000000 : ℝ)*base63 + (733250722712249/769850000000000000000000000 : ℝ)*base64 + (236339145455569/268650000000000000000000000 : ℝ)*base66 + (534812917263937/769850000000000000000000000 : ℝ)*base68 + (332950023501871011/1594590305000000000000000000000 : ℝ)*base70 + (10169603643903/13450000000000000000000000 : ℝ)*base72 + (576558054308899/805950000000000000000000000 : ℝ)*base74 + (779067649437009/1035650000000000000000000000 : ℝ)*base76 + (345363849072649/3613342500000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base85 + (1423/2500000000000000 : ℝ)*base87 + (1423/2500000000000000 : ℝ)*base89 + (1423/2500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2879/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2879/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (347357678542203115469421992243/51406402252590000000000000000000000 : ℝ) := by norm_num
    linear_combination (258291754909/1000000000000 : ℝ)*(base40) + (941288458829/1000000000000 : ℝ)*(base49) + (1255468349261/1000000000000 : ℝ)*(base59) + (1104103536253/100000000000 : ℝ)*(major_s2_0) + (1104103536253/100000000000 : ℝ)*(major_s2_1) + (1104103536253/100000000000 : ℝ)*(major_s2_2) + (35696883/1000000000000 : ℝ)*(sp_s2_0) + (28513071/500000000000 : ℝ)*(sp_s2_2) + (8959277/500000000000 : ℝ)*(sp_s2_16) + (98505949/500000000000 : ℝ)*(sp_s2_20) + (16200381719699/1000000000000 : ℝ)*(sp_s2_21) + (8100208708291/500000000000 : ℝ)*(sp_s2_22) + (8100171235943/500000000000 : ℝ)*(sp_s2_23) + (1470363511053/250000000000 : ℝ)*(sp_s2_27) + (588165105611/100000000000 : ℝ)*(f.failure) + (8100208708291/500000000000 : ℝ)*(f.sum) + (30392254744565381/1861381822500000000000000000000 : ℝ)*base63 + (15871349114081/23095500000000000000000000 : ℝ)*base65 + (45771930073499/161190000000000000000000000 : ℝ)*base67 + (5919668655421/18476400000000000000000000 : ℝ)*base69 + (4728230380949077/47837709150000000000000000000 : ℝ)*base70 + (2126258404813/2690000000000000000000000 : ℝ)*base73 + (149365809208523/483570000000000000000000000 : ℝ)*base75 + (37989663700243/207130000000000000000000000 : ℝ)*base76 + (10611272770314131/21680055000000000000000000000 : ℝ)*base79 + (77/250000000000000 : ℝ)*base86 + (77/250000000000000 : ℝ)*base88 + (77/250000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, false, true]])
    (hprev1 : (0 : ℝ) ≤ ((20713/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20713/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48357/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(48357/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46191/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(46191/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((1179/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(1179/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(5911/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(5911/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(2879/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(2879/12500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c320053_s2 p hpa hpb X hX hprev1

#print axioms solution
