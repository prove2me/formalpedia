-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c328054_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:22:40.718975+00:00
-- url     : https://prove2.me/submissions/95eedbfc-573c-4725-88ce-3c70dd3af2cb

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
theorem collision_support_c328054_s1_s1_0 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-113255639/1250000000 : ℝ)*x 0 + (4560399071/10000000000 : ℝ)*x 1 + (-6165472851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (113255639/1250000000 : ℝ)^93 ≤ (1375288113639/25000000000000 : ℝ)^77 := by
    have hnat : (113255639 : ℕ)^93*25000000000000^77 ≤ 1375288113639^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113255639 1250000000 1375288113639 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4560399071/10000000000 : ℝ)^93 ≤ (38738811952031/100000000000000 : ℝ)^77 := by
    have hnat : (4560399071 : ℕ)^93*100000000000000^77 ≤ 38738811952031^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4560399071 10000000000 38738811952031 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6165472851/10000000000 : ℝ)^93 ≤ (55760035570337/100000000000000 : ℝ)^77 := by
    have hnat : (6165472851 : ℕ)^93*100000000000000^77 ≤ 55760035570337^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6165472851 10000000000 55760035570337 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-113255639/1250000000 : ℝ), (4560399071/10000000000 : ℝ), (-6165472851/10000000000 : ℝ)] ![(1375288113639/25000000000000 : ℝ), (38738811952031/100000000000000 : ℝ), (55760035570337/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-113255639/1250000000 : ℝ)|^93 ≤ (1375288113639/25000000000000 : ℝ)^77
        have hw : |(-113255639/1250000000 : ℝ)|=(113255639/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4560399071/10000000000 : ℝ)|^93 ≤ (38738811952031/100000000000000 : ℝ)^77
        have hw : |(4560399071/10000000000 : ℝ)|=(4560399071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6165472851/10000000000 : ℝ)|^93 ≤ (55760035570337/100000000000000 : ℝ)^77
        have hw : |(-6165472851/10000000000 : ℝ)|=(6165472851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328054_s1_s1_2 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5060168989/10000000000 : ℝ)*x 0 + (2519708457/5000000000 : ℝ)*x 1 + (1772388811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5060168989/10000000000 : ℝ)^93 ≤ (4392308312533/10000000000000 : ℝ)^77 := by
    have hnat : (5060168989 : ℕ)^93*10000000000000^77 ≤ 4392308312533^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5060168989 10000000000 4392308312533 10000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2519708457/5000000000 : ℝ)^93 ≤ (4370561467397/10000000000000 : ℝ)^77 := by
    have hnat : (2519708457 : ℕ)^93*10000000000000^77 ≤ 4370561467397^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2519708457 5000000000 4370561467397 10000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1772388811/10000000000 : ℝ)^93 ≤ (618565109219/5000000000000 : ℝ)^77 := by
    have hnat : (1772388811 : ℕ)^93*5000000000000^77 ≤ 618565109219^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1772388811 10000000000 618565109219 5000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5060168989/10000000000 : ℝ), (2519708457/5000000000 : ℝ), (1772388811/10000000000 : ℝ)] ![(4392308312533/10000000000000 : ℝ), (4370561467397/10000000000000 : ℝ), (618565109219/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5060168989/10000000000 : ℝ)|^93 ≤ (4392308312533/10000000000000 : ℝ)^77
        have hw : |(5060168989/10000000000 : ℝ)|=(5060168989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2519708457/5000000000 : ℝ)|^93 ≤ (4370561467397/10000000000000 : ℝ)^77
        have hw : |(2519708457/5000000000 : ℝ)|=(2519708457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1772388811/10000000000 : ℝ)|^93 ≤ (618565109219/5000000000000 : ℝ)^77
        have hw : |(1772388811/10000000000 : ℝ)|=(1772388811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328054_s1_s1_6 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5181179047/10000000000 : ℝ)*x 0 + (12909007/25000000 : ℝ)*x 1 + (-1460861323/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5181179047/10000000000 : ℝ)^93 ≤ (22597432266061/50000000000000 : ℝ)^77 := by
    have hnat : (5181179047 : ℕ)^93*50000000000000^77 ≤ 22597432266061^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181179047 10000000000 22597432266061 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12909007/25000000 : ℝ)^93 ≤ (2813109771557/6250000000000 : ℝ)^77 := by
    have hnat : (12909007 : ℕ)^93*6250000000000^77 ≤ 2813109771557^77*25000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12909007 25000000 2813109771557 6250000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1460861323/10000000000 : ℝ)^93 ≤ (4897689553131/50000000000000 : ℝ)^77 := by
    have hnat : (1460861323 : ℕ)^93*50000000000000^77 ≤ 4897689553131^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1460861323 10000000000 4897689553131 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5181179047/10000000000 : ℝ), (12909007/25000000 : ℝ), (-1460861323/10000000000 : ℝ)] ![(22597432266061/50000000000000 : ℝ), (2813109771557/6250000000000 : ℝ), (4897689553131/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5181179047/10000000000 : ℝ)|^93 ≤ (22597432266061/50000000000000 : ℝ)^77
        have hw : |(5181179047/10000000000 : ℝ)|=(5181179047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(12909007/25000000 : ℝ)|^93 ≤ (2813109771557/6250000000000 : ℝ)^77
        have hw : |(12909007/25000000 : ℝ)|=(12909007/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1460861323/10000000000 : ℝ)|^93 ≤ (4897689553131/50000000000000 : ℝ)^77
        have hw : |(-1460861323/10000000000 : ℝ)|=(1460861323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328054_s1_s1_7 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-855286353/10000000000 : ℝ)*x 0 + (4380482743/10000000000 : ℝ)*x 1 + (-318347927/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (855286353/10000000000 : ℝ)^93 ≤ (5131125561189/100000000000000 : ℝ)^77 := by
    have hnat : (855286353 : ℕ)^93*100000000000000^77 ≤ 5131125561189^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      855286353 10000000000 5131125561189 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4380482743/10000000000 : ℝ)^93 ≤ (922514161897/2500000000000 : ℝ)^77 := by
    have hnat : (4380482743 : ℕ)^93*2500000000000^77 ≤ 922514161897^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4380482743 10000000000 922514161897 2500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (318347927/500000000 : ℝ)^93 ≤ (28984153972813/50000000000000 : ℝ)^77 := by
    have hnat : (318347927 : ℕ)^93*50000000000000^77 ≤ 28984153972813^77*500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      318347927 500000000 28984153972813 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-855286353/10000000000 : ℝ), (4380482743/10000000000 : ℝ), (-318347927/500000000 : ℝ)] ![(5131125561189/100000000000000 : ℝ), (922514161897/2500000000000 : ℝ), (28984153972813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-855286353/10000000000 : ℝ)|^93 ≤ (5131125561189/100000000000000 : ℝ)^77
        have hw : |(-855286353/10000000000 : ℝ)|=(855286353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4380482743/10000000000 : ℝ)|^93 ≤ (922514161897/2500000000000 : ℝ)^77
        have hw : |(4380482743/10000000000 : ℝ)|=(4380482743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-318347927/500000000 : ℝ)|^93 ≤ (28984153972813/50000000000000 : ℝ)^77
        have hw : |(-318347927/500000000 : ℝ)|=(318347927/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328054_s1_s1_8 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5317461451/10000000000 : ℝ)*x 0 + (-1273098369/10000000000 : ℝ)*x 1 + (-5169288733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5317461451/10000000000 : ℝ)^93 ≤ (5829319570121/12500000000000 : ℝ)^77 := by
    have hnat : (5317461451 : ℕ)^93*12500000000000^77 ≤ 5829319570121^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5317461451 10000000000 5829319570121 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1273098369/10000000000 : ℝ)^93 ≤ (8295818705023/100000000000000 : ℝ)^77 := by
    have hnat : (1273098369 : ℕ)^93*100000000000000^77 ≤ 8295818705023^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1273098369 10000000000 8295818705023 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5169288733/10000000000 : ℝ)^93 ≤ (45069624719061/100000000000000 : ℝ)^77 := by
    have hnat : (5169288733 : ℕ)^93*100000000000000^77 ≤ 45069624719061^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169288733 10000000000 45069624719061 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5317461451/10000000000 : ℝ), (-1273098369/10000000000 : ℝ), (-5169288733/10000000000 : ℝ)] ![(5829319570121/12500000000000 : ℝ), (8295818705023/100000000000000 : ℝ), (45069624719061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5317461451/10000000000 : ℝ)|^93 ≤ (5829319570121/12500000000000 : ℝ)^77
        have hw : |(5317461451/10000000000 : ℝ)|=(5317461451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1273098369/10000000000 : ℝ)|^93 ≤ (8295818705023/100000000000000 : ℝ)^77
        have hw : |(-1273098369/10000000000 : ℝ)|=(1273098369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5169288733/10000000000 : ℝ)|^93 ≤ (45069624719061/100000000000000 : ℝ)^77
        have hw : |(-5169288733/10000000000 : ℝ)|=(5169288733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328054_s1_s1_9 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4897979993/10000000000 : ℝ)*x 0 + (5630367617/10000000000 : ℝ)*x 1 + (151262967/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4897979993/10000000000 : ℝ)^93 ≤ (42228432049267/100000000000000 : ℝ)^77 := by
    have hnat : (4897979993 : ℕ)^93*100000000000000^77 ≤ 42228432049267^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4897979993 10000000000 42228432049267 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5630367617/10000000000 : ℝ)^93 ≤ (49968951016537/100000000000000 : ℝ)^77 := by
    have hnat : (5630367617 : ℕ)^93*100000000000000^77 ≤ 49968951016537^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5630367617 10000000000 49968951016537 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (151262967/1250000000 : ℝ)^93 ≤ (1560523384257/20000000000000 : ℝ)^77 := by
    have hnat : (151262967 : ℕ)^93*20000000000000^77 ≤ 1560523384257^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151262967 1250000000 1560523384257 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4897979993/10000000000 : ℝ), (5630367617/10000000000 : ℝ), (151262967/1250000000 : ℝ)] ![(42228432049267/100000000000000 : ℝ), (49968951016537/100000000000000 : ℝ), (1560523384257/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4897979993/10000000000 : ℝ)|^93 ≤ (42228432049267/100000000000000 : ℝ)^77
        have hw : |(4897979993/10000000000 : ℝ)|=(4897979993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5630367617/10000000000 : ℝ)|^93 ≤ (49968951016537/100000000000000 : ℝ)^77
        have hw : |(5630367617/10000000000 : ℝ)|=(5630367617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(151262967/1250000000 : ℝ)|^93 ≤ (1560523384257/20000000000000 : ℝ)^77
        have hw : |(151262967/1250000000 : ℝ)|=(151262967/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328054_s1_s1_13 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1017578407/2000000000 : ℝ)*x 0 + (2856126179/5000000000 : ℝ)*x 1 + (-103570133/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1017578407/2000000000 : ℝ)^93 ≤ (44213892059609/100000000000000 : ℝ)^77 := by
    have hnat : (1017578407 : ℕ)^93*100000000000000^77 ≤ 44213892059609^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017578407 2000000000 44213892059609 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2856126179/5000000000 : ℝ)^93 ≤ (50847997637893/100000000000000 : ℝ)^77 := by
    have hnat : (2856126179 : ℕ)^93*100000000000000^77 ≤ 50847997637893^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2856126179 5000000000 50847997637893 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (103570133/1250000000 : ℝ)^93 ≤ (617263785677/12500000000000 : ℝ)^77 := by
    have hnat : (103570133 : ℕ)^93*12500000000000^77 ≤ 617263785677^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103570133 1250000000 617263785677 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1017578407/2000000000 : ℝ), (2856126179/5000000000 : ℝ), (-103570133/1250000000 : ℝ)] ![(44213892059609/100000000000000 : ℝ), (50847997637893/100000000000000 : ℝ), (617263785677/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1017578407/2000000000 : ℝ)|^93 ≤ (44213892059609/100000000000000 : ℝ)^77
        have hw : |(1017578407/2000000000 : ℝ)|=(1017578407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2856126179/5000000000 : ℝ)|^93 ≤ (50847997637893/100000000000000 : ℝ)^77
        have hw : |(2856126179/5000000000 : ℝ)|=(2856126179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-103570133/1250000000 : ℝ)|^93 ≤ (617263785677/12500000000000 : ℝ)^77
        have hw : |(-103570133/1250000000 : ℝ)|=(103570133/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328054_s1_s1_14 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-135590421/2500000000 : ℝ)*x 0 + (2312058483/5000000000 : ℝ)*x 1 + (-6337685743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135590421/2500000000 : ℝ)^93 ≤ (1479974122743/50000000000000 : ℝ)^77 := by
    have hnat : (135590421 : ℕ)^93*50000000000000^77 ≤ 1479974122743^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135590421 2500000000 1479974122743 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2312058483/5000000000 : ℝ)^93 ≤ (39393485456209/100000000000000 : ℝ)^77 := by
    have hnat : (2312058483 : ℕ)^93*100000000000000^77 ≤ 39393485456209^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2312058483 5000000000 39393485456209 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6337685743/10000000000 : ℝ)^93 ≤ (7205820786169/12500000000000 : ℝ)^77 := by
    have hnat : (6337685743 : ℕ)^93*12500000000000^77 ≤ 7205820786169^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6337685743 10000000000 7205820786169 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-135590421/2500000000 : ℝ), (2312058483/5000000000 : ℝ), (-6337685743/10000000000 : ℝ)] ![(1479974122743/50000000000000 : ℝ), (39393485456209/100000000000000 : ℝ), (7205820786169/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-135590421/2500000000 : ℝ)|^93 ≤ (1479974122743/50000000000000 : ℝ)^77
        have hw : |(-135590421/2500000000 : ℝ)|=(135590421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2312058483/5000000000 : ℝ)|^93 ≤ (39393485456209/100000000000000 : ℝ)^77
        have hw : |(2312058483/5000000000 : ℝ)|=(2312058483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6337685743/10000000000 : ℝ)|^93 ≤ (7205820786169/12500000000000 : ℝ)^77
        have hw : |(-6337685743/10000000000 : ℝ)|=(6337685743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328054_s1_s1_15 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5080812619/10000000000 : ℝ)*x 0 + (-62458273/400000000 : ℝ)*x 1 + (-1296475407/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5080812619/10000000000 : ℝ)^93 ≤ (22069799546099/50000000000000 : ℝ)^77 := by
    have hnat : (5080812619 : ℕ)^93*50000000000000^77 ≤ 22069799546099^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5080812619 10000000000 22069799546099 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (62458273/400000000 : ℝ)^93 ≤ (10615777181321/100000000000000 : ℝ)^77 := by
    have hnat : (62458273 : ℕ)^93*100000000000000^77 ≤ 10615777181321^77*400000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62458273 400000000 10615777181321 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1296475407/2500000000 : ℝ)^93 ≤ (45244623715369/100000000000000 : ℝ)^77 := by
    have hnat : (1296475407 : ℕ)^93*100000000000000^77 ≤ 45244623715369^77*2500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296475407 2500000000 45244623715369 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5080812619/10000000000 : ℝ), (-62458273/400000000 : ℝ), (-1296475407/2500000000 : ℝ)] ![(22069799546099/50000000000000 : ℝ), (10615777181321/100000000000000 : ℝ), (45244623715369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5080812619/10000000000 : ℝ)|^93 ≤ (22069799546099/50000000000000 : ℝ)^77
        have hw : |(5080812619/10000000000 : ℝ)|=(5080812619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-62458273/400000000 : ℝ)|^93 ≤ (10615777181321/100000000000000 : ℝ)^77
        have hw : |(-62458273/400000000 : ℝ)|=(62458273/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1296475407/2500000000 : ℝ)|^93 ≤ (45244623715369/100000000000000 : ℝ)^77
        have hw : |(-1296475407/2500000000 : ℝ)|=(1296475407/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328054_s1_s1_16 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2832793071/5000000000 : ℝ)*x 0 + (609262197/1250000000 : ℝ)*x 1 + (1193491049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2832793071/5000000000 : ℝ)^93 ≤ (50346704563393/100000000000000 : ℝ)^77 := by
    have hnat : (2832793071 : ℕ)^93*100000000000000^77 ≤ 50346704563393^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2832793071 5000000000 50346704563393 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (609262197/1250000000 : ℝ)^93 ≤ (4197986812381/10000000000000 : ℝ)^77 := by
    have hnat : (609262197 : ℕ)^93*10000000000000^77 ≤ 4197986812381^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      609262197 1250000000 4197986812381 10000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1193491049/10000000000 : ℝ)^93 ≤ (1534685458983/20000000000000 : ℝ)^77 := by
    have hnat : (1193491049 : ℕ)^93*20000000000000^77 ≤ 1534685458983^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1193491049 10000000000 1534685458983 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2832793071/5000000000 : ℝ), (609262197/1250000000 : ℝ), (1193491049/10000000000 : ℝ)] ![(50346704563393/100000000000000 : ℝ), (4197986812381/10000000000000 : ℝ), (1534685458983/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2832793071/5000000000 : ℝ)|^93 ≤ (50346704563393/100000000000000 : ℝ)^77
        have hw : |(2832793071/5000000000 : ℝ)|=(2832793071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(609262197/1250000000 : ℝ)|^93 ≤ (4197986812381/10000000000000 : ℝ)^77
        have hw : |(609262197/1250000000 : ℝ)|=(609262197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1193491049/10000000000 : ℝ)|^93 ≤ (1534685458983/20000000000000 : ℝ)^77
        have hw : |(1193491049/10000000000 : ℝ)|=(1193491049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328054_s1_s1_20 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2848092273/5000000000 : ℝ)*x 0 + (2518225461/5000000000 : ℝ)*x 1 + (-926316721/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2848092273/5000000000 : ℝ)^93 ≤ (50675299203297/100000000000000 : ℝ)^77 := by
    have hnat : (2848092273 : ℕ)^93*100000000000000^77 ≤ 50675299203297^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2848092273 5000000000 50675299203297 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2518225461/5000000000 : ℝ)^93 ≤ (43674548155901/100000000000000 : ℝ)^77 := by
    have hnat : (2518225461 : ℕ)^93*100000000000000^77 ≤ 43674548155901^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2518225461 5000000000 43674548155901 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (926316721/10000000000 : ℝ)^93 ≤ (226006105153/4000000000000 : ℝ)^77 := by
    have hnat : (926316721 : ℕ)^93*4000000000000^77 ≤ 226006105153^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      926316721 10000000000 226006105153 4000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2848092273/5000000000 : ℝ), (2518225461/5000000000 : ℝ), (-926316721/10000000000 : ℝ)] ![(50675299203297/100000000000000 : ℝ), (43674548155901/100000000000000 : ℝ), (226006105153/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2848092273/5000000000 : ℝ)|^93 ≤ (50675299203297/100000000000000 : ℝ)^77
        have hw : |(2848092273/5000000000 : ℝ)|=(2848092273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2518225461/5000000000 : ℝ)|^93 ≤ (43674548155901/100000000000000 : ℝ)^77
        have hw : |(2518225461/5000000000 : ℝ)|=(2518225461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-926316721/10000000000 : ℝ)|^93 ≤ (226006105153/4000000000000 : ℝ)^77
        have hw : |(-926316721/10000000000 : ℝ)|=(926316721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328054_s1_s1_21 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-365273367/10000000000 : ℝ)*x 0 + (2517093627/5000000000 : ℝ)*x 1 + (-605107509/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (365273367/10000000000 : ℝ)^93 ≤ (183628983559/10000000000000 : ℝ)^77 := by
    have hnat : (365273367 : ℕ)^93*10000000000000^77 ≤ 183628983559^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      365273367 10000000000 183628983559 10000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2517093627/5000000000 : ℝ)^93 ≤ (43650840507041/100000000000000 : ℝ)^77 := by
    have hnat : (2517093627 : ℕ)^93*100000000000000^77 ≤ 43650840507041^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2517093627 5000000000 43650840507041 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (605107509/1000000000 : ℝ)^93 ≤ (27256434821819/50000000000000 : ℝ)^77 := by
    have hnat : (605107509 : ℕ)^93*50000000000000^77 ≤ 27256434821819^77*1000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      605107509 1000000000 27256434821819 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-365273367/10000000000 : ℝ), (2517093627/5000000000 : ℝ), (-605107509/1000000000 : ℝ)] ![(183628983559/10000000000000 : ℝ), (43650840507041/100000000000000 : ℝ), (27256434821819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-365273367/10000000000 : ℝ)|^93 ≤ (183628983559/10000000000000 : ℝ)^77
        have hw : |(-365273367/10000000000 : ℝ)|=(365273367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2517093627/5000000000 : ℝ)|^93 ≤ (43650840507041/100000000000000 : ℝ)^77
        have hw : |(2517093627/5000000000 : ℝ)|=(2517093627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-605107509/1000000000 : ℝ)|^93 ≤ (27256434821819/50000000000000 : ℝ)^77
        have hw : |(-605107509/1000000000 : ℝ)|=(605107509/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328054_s1_s1_22 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3003783061/5000000000 : ℝ)*x 0 + (-17058857/125000000 : ℝ)*x 1 + (-4384169477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3003783061/5000000000 : ℝ)^93 ≤ (54039813887161/100000000000000 : ℝ)^77 := by
    have hnat : (3003783061 : ℕ)^93*100000000000000^77 ≤ 54039813887161^77*5000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3003783061 5000000000 54039813887161 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (17058857/125000000 : ℝ)^93 ≤ (2255526628597/25000000000000 : ℝ)^77 := by
    have hnat : (17058857 : ℕ)^93*25000000000000^77 ≤ 2255526628597^77*125000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17058857 125000000 2255526628597 25000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4384169477/10000000000 : ℝ)^93 ≤ (4617259948039/12500000000000 : ℝ)^77 := by
    have hnat : (4384169477 : ℕ)^93*12500000000000^77 ≤ 4617259948039^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4384169477 10000000000 4617259948039 12500000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3003783061/5000000000 : ℝ), (-17058857/125000000 : ℝ), (-4384169477/10000000000 : ℝ)] ![(54039813887161/100000000000000 : ℝ), (2255526628597/25000000000000 : ℝ), (4617259948039/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3003783061/5000000000 : ℝ)|^93 ≤ (54039813887161/100000000000000 : ℝ)^77
        have hw : |(3003783061/5000000000 : ℝ)|=(3003783061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-17058857/125000000 : ℝ)|^93 ≤ (2255526628597/25000000000000 : ℝ)^77
        have hw : |(-17058857/125000000 : ℝ)|=(17058857/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4384169477/10000000000 : ℝ)|^93 ≤ (4617259948039/12500000000000 : ℝ)^77
        have hw : |(-4384169477/10000000000 : ℝ)|=(4384169477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328054_s1_s1_23 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (625968709/1250000000 : ℝ)*x 0 + (253232087/500000000 : ℝ)*x 1 + (28220017/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (625968709/1250000000 : ℝ)^93 ≤ (43374120955467/100000000000000 : ℝ)^77 := by
    have hnat : (625968709 : ℕ)^93*100000000000000^77 ≤ 43374120955467^77*1250000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      625968709 1250000000 43374120955467 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (253232087/500000000 : ℝ)^93 ≤ (21984989498559/50000000000000 : ℝ)^77 := by
    have hnat : (253232087 : ℕ)^93*50000000000000^77 ≤ 21984989498559^77*500000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253232087 500000000 21984989498559 50000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (28220017/156250000 : ℝ)^93 ≤ (12655900046327/100000000000000 : ℝ)^77 := by
    have hnat : (28220017 : ℕ)^93*100000000000000^77 ≤ 12655900046327^77*156250000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      28220017 156250000 12655900046327 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(625968709/1250000000 : ℝ), (253232087/500000000 : ℝ), (28220017/156250000 : ℝ)] ![(43374120955467/100000000000000 : ℝ), (21984989498559/50000000000000 : ℝ), (12655900046327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(625968709/1250000000 : ℝ)|^93 ≤ (43374120955467/100000000000000 : ℝ)^77
        have hw : |(625968709/1250000000 : ℝ)|=(625968709/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(253232087/500000000 : ℝ)|^93 ≤ (21984989498559/50000000000000 : ℝ)^77
        have hw : |(253232087/500000000 : ℝ)|=(253232087/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(28220017/156250000 : ℝ)|^93 ≤ (12655900046327/100000000000000 : ℝ)^77
        have hw : |(28220017/156250000 : ℝ)|=(28220017/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c328054_s1_s1_27 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5389522701/10000000000 : ℝ)*x 0 + (5112516827/10000000000 : ℝ)*x 1 + (-250362647/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5389522701/10000000000 : ℝ)^93 ≤ (9479786283253/20000000000000 : ℝ)^77 := by
    have hnat : (5389522701 : ℕ)^93*20000000000000^77 ≤ 9479786283253^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389522701 10000000000 9479786283253 20000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5112516827/10000000000 : ℝ)^93 ≤ (44472477282629/100000000000000 : ℝ)^77 := by
    have hnat : (5112516827 : ℕ)^93*100000000000000^77 ≤ 44472477282629^77*10000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5112516827 10000000000 44472477282629 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (250362647/2000000000 : ℝ)^93 ≤ (8128591284257/100000000000000 : ℝ)^77 := by
    have hnat : (250362647 : ℕ)^93*100000000000000^77 ≤ 8128591284257^77*2000000000^93 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250362647 2000000000 8128591284257 100000000000000 93 77 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (93/16 : ℝ)) 93 77 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5389522701/10000000000 : ℝ), (5112516827/10000000000 : ℝ), (-250362647/2000000000 : ℝ)] ![(9479786283253/20000000000000 : ℝ), (44472477282629/100000000000000 : ℝ), (8128591284257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5389522701/10000000000 : ℝ)|^93 ≤ (9479786283253/20000000000000 : ℝ)^77
        have hw : |(5389522701/10000000000 : ℝ)|=(5389522701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5112516827/10000000000 : ℝ)|^93 ≤ (44472477282629/100000000000000 : ℝ)^77
        have hw : |(5112516827/10000000000 : ℝ)|=(5112516827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-250362647/2000000000 : ℝ)|^93 ≤ (8128591284257/100000000000000 : ℝ)^77
        have hw : |(-250362647/2000000000 : ℝ)|=(250362647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c328054_s1 (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((5953/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5953/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12537/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(12537/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1381/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1381/2500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((26847/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26847/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3557/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3557/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8969/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-8969/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (82433/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (82433/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (82433/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (82433/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (82433/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (82433/100000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (5953/10000 : ℝ) ^ (91/16 : ℝ) ≤ (5233718162317584933/100000000000000000000 : ℝ) := by
    have hpowers : (5953/10000 : ℝ)^91 ≤ (5233718162317584933/100000000000000000000 : ℝ)^16 := by
      have hnat : (5953 : ℕ)^91*100000000000000000000^16 ≤ 5233718162317584933^16*10000^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5953 10000 5233718162317584933 100000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5953/10000 : ℝ)) (X := (5233718162317584933/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (105233718162317584933/100000000000000000000 : ℝ) ≤ (1009009766060651/1000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (105233718162317584933/100000000000000000000 : ℝ)^16 ≤ (1009009766060651/1000000000000000 : ℝ)^91 := by
      have hnat : (105233718162317584933 : ℕ)^16*1000000000000000^91 ≤ 1009009766060651^91*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        105233718162317584933 100000000000000000000 1009009766060651 1000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1009009766060651/1000000000000000 : ℝ)) (X := (105233718162317584933/100000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (55233718162317584933/50000000000000000000 : ℝ) ≤ (5088287419977073/5000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (55233718162317584933/50000000000000000000 : ℝ)^16 ≤ (5088287419977073/5000000000000000 : ℝ)^91 := by
      have hnat : (55233718162317584933 : ℕ)^16*5000000000000000^91 ≤ 5088287419977073^91*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        55233718162317584933 50000000000000000000 5088287419977073 5000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5088287419977073/5000000000000000 : ℝ)) (X := (55233718162317584933/50000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(9009766060651/595300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(21619294836909/1488250000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (5953/10000 : ℝ)) (alpha := (9009766060651/595300000000000 : ℝ)) (beta := (21619294836909/1488250000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (5953/10000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(9009766060651/595300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(21619294836909/1488250000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (12537/20000 : ℝ) ^ (91/16 : ℝ) ≤ (7020501666236512283/100000000000000000000 : ℝ) := by
    have hpowers : (12537/20000 : ℝ)^91 ≤ (7020501666236512283/100000000000000000000 : ℝ)^16 := by
      have hnat : (12537 : ℕ)^91*100000000000000000000^16 ≤ 7020501666236512283^16*20000^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12537 20000 7020501666236512283 100000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12537/20000 : ℝ)) (X := (7020501666236512283/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (107020501666236512283/100000000000000000000 : ℝ) ≤ (63250072148759/62500000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (107020501666236512283/100000000000000000000 : ℝ)^16 ≤ (63250072148759/62500000000000 : ℝ)^91 := by
      have hnat : (107020501666236512283 : ℕ)^16*62500000000000^91 ≤ 63250072148759^91*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        107020501666236512283 100000000000000000000 63250072148759 62500000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (63250072148759/62500000000000 : ℝ)) (X := (107020501666236512283/100000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (57020501666236512283/50000000000000000000 : ℝ) ≤ (5116850317855133/5000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (57020501666236512283/50000000000000000000 : ℝ)^16 ≤ (5116850317855133/5000000000000000 : ℝ)^91 := by
      have hnat : (57020501666236512283 : ℕ)^16*5000000000000000^91 ≤ 5116850317855133^91*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57020501666236512283 50000000000000000000 5116850317855133 5000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5116850317855133/5000000000000000 : ℝ)) (X := (57020501666236512283/50000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(750072148759/39178125000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(8120649422059/447750000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (12537/20000 : ℝ)) (alpha := (750072148759/39178125000000 : ℝ)) (beta := (8120649422059/447750000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (12537/20000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(750072148759/39178125000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(8120649422059/447750000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (1381/2500 : ℝ) ^ (91/16 : ℝ) ≤ (342032793621000931/10000000000000000000 : ℝ) := by
    have hpowers : (1381/2500 : ℝ)^91 ≤ (342032793621000931/10000000000000000000 : ℝ)^16 := by
      have hnat : (1381 : ℕ)^91*10000000000000000000^16 ≤ 342032793621000931^16*2500^91 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1381 2500 342032793621000931 10000000000000000000 91 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1381/2500 : ℝ)) (X := (342032793621000931/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (10342032793621000931/10000000000000000000 : ℝ) ≤ (5029653611172349/5000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (10342032793621000931/10000000000000000000 : ℝ)^16 ≤ (5029653611172349/5000000000000000 : ℝ)^91 := by
      have hnat : (10342032793621000931 : ℕ)^16*5000000000000000^91 ≤ 5029653611172349^91*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10342032793621000931 10000000000000000000 5029653611172349 5000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5029653611172349/5000000000000000 : ℝ)) (X := (10342032793621000931/10000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (5342032793621000931/5000000000000000000 : ℝ) ≤ (5058509660749607/5000000000000000 : ℝ) ^ (91/16 : ℝ) := by
    have hpowers : (5342032793621000931/5000000000000000000 : ℝ)^16 ≤ (5058509660749607/5000000000000000 : ℝ)^91 := by
      have hnat : (5342032793621000931 : ℕ)^16*5000000000000000^91 ≤ 5058509660749607^91*5000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5342032793621000931 5000000000000000000 5058509660749607 5000000000000000 16 91 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5058509660749607/5000000000000000 : ℝ)) (X := (5342032793621000931/5000000000000000000 : ℝ)) (by norm_num) 91 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(29653611172349/2762000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(14428024788629/1381000000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (91/16 : ℝ)) (rho := (1381/2500 : ℝ)) (alpha := (29653611172349/2762000000000000 : ℝ)) (beta := (14428024788629/1381000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (1381/2500 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(29653611172349/2762000000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(14428024788629/1381000000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-113255639/1250000000 : ℝ)*X 0 0+(4560399071/10000000000 : ℝ)*X 0 1+(-6165472851/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328054_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((5060168989/10000000000 : ℝ)*X 2 0+(2519708457/5000000000 : ℝ)*X 2 1+(1772388811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328054_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((5181179047/10000000000 : ℝ)*X 0 0+(12909007/25000000 : ℝ)*X 0 1+(-1460861323/10000000000 : ℝ)*X 0 2+(5181179047/10000000000 : ℝ)*X 1 0+(12909007/25000000 : ℝ)*X 1 1+(-1460861323/10000000000 : ℝ)*X 1 2+(5181179047/10000000000 : ℝ)*X 2 0+(12909007/25000000 : ℝ)*X 2 1+(-1460861323/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328054_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-855286353/10000000000 : ℝ)*X 0 0+(4380482743/10000000000 : ℝ)*X 0 1+(-318347927/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328054_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((5317461451/10000000000 : ℝ)*X 1 0+(-1273098369/10000000000 : ℝ)*X 1 1+(-5169288733/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328054_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4897979993/10000000000 : ℝ)*X 2 0+(5630367617/10000000000 : ℝ)*X 2 1+(151262967/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328054_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((1017578407/2000000000 : ℝ)*X 0 0+(2856126179/5000000000 : ℝ)*X 0 1+(-103570133/1250000000 : ℝ)*X 0 2+(1017578407/2000000000 : ℝ)*X 1 0+(2856126179/5000000000 : ℝ)*X 1 1+(-103570133/1250000000 : ℝ)*X 1 2+(1017578407/2000000000 : ℝ)*X 2 0+(2856126179/5000000000 : ℝ)*X 2 1+(-103570133/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328054_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-135590421/2500000000 : ℝ)*X 0 0+(2312058483/5000000000 : ℝ)*X 0 1+(-6337685743/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328054_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((5080812619/10000000000 : ℝ)*X 1 0+(-62458273/400000000 : ℝ)*X 1 1+(-1296475407/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328054_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((2832793071/5000000000 : ℝ)*X 2 0+(609262197/1250000000 : ℝ)*X 2 1+(1193491049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328054_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((2848092273/5000000000 : ℝ)*X 0 0+(2518225461/5000000000 : ℝ)*X 0 1+(-926316721/10000000000 : ℝ)*X 0 2+(2848092273/5000000000 : ℝ)*X 1 0+(2518225461/5000000000 : ℝ)*X 1 1+(-926316721/10000000000 : ℝ)*X 1 2+(2848092273/5000000000 : ℝ)*X 2 0+(2518225461/5000000000 : ℝ)*X 2 1+(-926316721/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328054_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-365273367/10000000000 : ℝ)*X 0 0+(2517093627/5000000000 : ℝ)*X 0 1+(-605107509/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c328054_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((3003783061/5000000000 : ℝ)*X 1 0+(-17058857/125000000 : ℝ)*X 1 1+(-4384169477/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c328054_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((625968709/1250000000 : ℝ)*X 2 0+(253232087/500000000 : ℝ)*X 2 1+(28220017/156250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c328054_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((5389522701/10000000000 : ℝ)*X 0 0+(5112516827/10000000000 : ℝ)*X 0 1+(-250362647/2000000000 : ℝ)*X 0 2+(5389522701/10000000000 : ℝ)*X 1 0+(5112516827/10000000000 : ℝ)*X 1 1+(-250362647/2000000000 : ℝ)*X 1 2+(5389522701/10000000000 : ℝ)*X 2 0+(5112516827/10000000000 : ℝ)*X 2 1+(-250362647/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c328054_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((26847/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26847/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (193003489616286323546959129619/34355947647000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1573581/250000000000 : ℝ)*(base23) + (330548512399/250000000000 : ℝ)*(base39) + (79516342427/125000000000 : ℝ)*(base60) + (8717446497073/1000000000000 : ℝ)*(major_s1_0) + (8717446497073/1000000000000 : ℝ)*(major_s1_1) + (8717446497073/1000000000000 : ℝ)*(major_s1_2) + (3629447/250000000000 : ℝ)*(sp_s1_6) + (536685839397/40000000000 : ℝ)*(sp_s1_7) + (13417107129703/1000000000000 : ℝ)*(sp_s1_8) + (6708565178203/500000000000 : ℝ)*(sp_s1_9) + (2008852401683/500000000000 : ℝ)*(sp_s1_13) + (6453869/250000000000 : ℝ)*(sp_s1_14) + (64670699/1000000000000 : ℝ)*(sp_s1_15) + (35149671/1000000000000 : ℝ)*(sp_s1_23) + (2008859660577/500000000000 : ℝ)*(f.failure) + (13417171800401/1000000000000 : ℝ)*(f.sum) + (13207313234162156771/34627194000000000000000000000000 : ℝ)*base62 + (152048810709017/1381000000000000000000000000 : ℝ)*base65 + (78068990114407/447750000000000000000000000 : ℝ)*base66 + (1892543026561523/2762000000000000000000000000 : ℝ)*base68 + (186565115535849731/8221093000000000000000000000000 : ℝ)*base71 + (158615451871/186031250000000000000000000 : ℝ)*base72 + (42136400825237/156712500000000000000000000 : ℝ)*base74 + (139614155045423/595300000000000000000000000 : ℝ)*base77 + (238873006635077971/666363937500000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (1783/2000000000000000 : ℝ)*base87 + (1783/2000000000000000 : ℝ)*base89 + (1783/2000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3557/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3557/12500 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (17335235523150121125669650157/2862995637250000000000000000000000 : ℝ) := by norm_num
    linear_combination (6858679/1000000000000 : ℝ)*(base21) + (19583010919/15625000000 : ℝ)*(base39) + (146415633359/500000000000 : ℝ)*(base60) + (67709799921/7812500000 : ℝ)*(major_s1_0) + (67709799921/7812500000 : ℝ)*(major_s1_1) + (67709799921/7812500000 : ℝ)*(major_s1_2) + (285159/7812500000 : ℝ)*(sp_s1_2) + (12482889/200000000000 : ℝ)*(sp_s1_7) + (23921787/1000000000000 : ℝ)*(sp_s1_8) + (666962102363/50000000000 : ℝ)*(sp_s1_14) + (13339280539917/1000000000000 : ℝ)*(sp_s1_15) + (6669630551337/500000000000 : ℝ)*(sp_s1_16) + (1997184443853/500000000000 : ℝ)*(sp_s1_20) + (16706023/500000000000 : ℝ)*(sp_s1_27) + (499300287469/125000000000 : ℝ)*(f.failure) + (1667413057713/125000000000 : ℝ)*(f.sum) + (614038347940299301/1442799750000000000000000000000 : ℝ)*base63 + (39104133746163/345250000000000000000000000 : ℝ)*base65 + (1536305726291/37312500000000000000000000 : ℝ)*base66 + (166809506644907/172625000000000000000000000 : ℝ)*base69 + (65698175479919683/1027636625000000000000000000000 : ℝ)*base70 + (901834670383833/1488250000000000000000000000 : ℝ)*base72 + (11624833955107/104475000000000000000000000 : ℝ)*base75 + (63846440738077/148825000000000000000000000 : ℝ)*base77 + (27590202012581059/444242625000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (549/500000000000000 : ℝ)*base86 + (549/500000000000000 : ℝ)*base88 + (549/500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8969/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-8969/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13101259861432517398185138119/1717797382350000000000000000000000 : ℝ) := by norm_num
    linear_combination (2731363/500000000000 : ℝ)*(base11) + (344891058097/250000000000 : ℝ)*(base39) + (394889/1000000000000 : ℝ)*(base50) + (616172246903/100000000000 : ℝ)*(major_s1_0) + (616172246903/100000000000 : ℝ)*(major_s1_1) + (616172246903/100000000000 : ℝ)*(major_s1_2) + (6642507/250000000000 : ℝ)*(sp_s1_0) + (7074163/31250000000 : ℝ)*(sp_s1_2) + (37044097/1000000000000 : ℝ)*(sp_s1_9) + (1333687/50000000000 : ℝ)*(sp_s1_20) + (9483579751661/1000000000000 : ℝ)*(sp_s1_21) + (4741805892207/500000000000 : ℝ)*(sp_s1_22) + (4741674183551/500000000000 : ℝ)*(sp_s1_23) + (567960787527/200000000000 : ℝ)*(sp_s1_27) + (1419915305687/500000000000 : ℝ)*(f.failure) + (4741805892207/500000000000 : ℝ)*(f.sum) + (2044184775110821261/3462719400000000000000000000000 : ℝ)*base62 + (85120484823683/138100000000000000000000000 : ℝ)*base64 + (29209937823289/89550000000000000000000000 : ℝ)*base66 + (29557590100687/276200000000000000000000000 : ℝ)*base69 + (243187589391703509/822109300000000000000000000000 : ℝ)*base70 + (27185128723549/297650000000000000000000000 : ℝ)*base73 + (11905469431813/15671250000000000000000000 : ℝ)*base74 + (25806596821781/59530000000000000000000000 : ℝ)*base76 + (9004106897285233/533091150000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (2527/2000000000000000 : ℝ)*base86 + (2527/2000000000000000 : ℝ)*base88 + (2527/2000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (91/16 : ℝ) ≤ p) (hpb : p ≤ (93/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (8679/4000 : ℝ) (80697/50000 : ℝ) (82433/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, false], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((5953/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5953/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12537/20000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(12537/20000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-1381/2500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-1381/2500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((26847/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(26847/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(3557/12500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(3557/12500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8969/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-8969/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c328054_s1 p hpa hpb X hX hprev0

#print axioms solution
