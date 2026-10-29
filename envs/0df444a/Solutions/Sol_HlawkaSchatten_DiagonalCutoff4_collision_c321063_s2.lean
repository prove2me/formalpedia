-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c321063_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:42:32.438553+00:00
-- url     : https://prove2.me/submissions/f458eed3-de82-47c9-bd53-26a35b5984c3

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
theorem collision_support_c321063_s2_s2_0 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-1338470937/10000000000 : ℝ)*x 0 + (2667587993/5000000000 : ℝ)*x 1 + (2674656601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338470937/10000000000 : ℝ)^41 ≤ (4110056434607/50000000000000 : ℝ)^33 := by
    have hnat : (1338470937 : ℕ)^41*50000000000000^33 ≤ 4110056434607^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338470937 10000000000 4110056434607 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2667587993/5000000000 : ℝ)^41 ≤ (11453626074361/25000000000000 : ℝ)^33 := by
    have hnat : (2667587993 : ℕ)^41*25000000000000^33 ≤ 11453626074361^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2667587993 5000000000 11453626074361 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2674656601/5000000000 : ℝ)^41 ≤ (22982691410909/50000000000000 : ℝ)^33 := by
    have hnat : (2674656601 : ℕ)^41*50000000000000^33 ≤ 22982691410909^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674656601 5000000000 22982691410909 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1338470937/10000000000 : ℝ), (2667587993/5000000000 : ℝ), (2674656601/5000000000 : ℝ)] ![(4110056434607/50000000000000 : ℝ), (11453626074361/25000000000000 : ℝ), (22982691410909/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1338470937/10000000000 : ℝ)|^41 ≤ (4110056434607/50000000000000 : ℝ)^33
        have hw : |(-1338470937/10000000000 : ℝ)|=(1338470937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2667587993/5000000000 : ℝ)|^41 ≤ (11453626074361/25000000000000 : ℝ)^33
        have hw : |(2667587993/5000000000 : ℝ)|=(2667587993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2674656601/5000000000 : ℝ)|^41 ≤ (22982691410909/50000000000000 : ℝ)^33
        have hw : |(2674656601/5000000000 : ℝ)|=(2674656601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321063_s2_s2_1 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5335669299/10000000000 : ℝ)*x 0 + (-1342448917/10000000000 : ℝ)*x 1 + (2672987891/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5335669299/10000000000 : ℝ)^41 ≤ (4581976751821/10000000000000 : ℝ)^33 := by
    have hnat : (5335669299 : ℕ)^41*10000000000000^33 ≤ 4581976751821^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5335669299 10000000000 4581976751821 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1342448917/10000000000 : ℝ)^41 ≤ (2062619194097/25000000000000 : ℝ)^33 := by
    have hnat : (1342448917 : ℕ)^41*25000000000000^33 ≤ 2062619194097^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342448917 10000000000 2062619194097 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2672987891/5000000000 : ℝ)^41 ≤ (45929755696081/100000000000000 : ℝ)^33 := by
    have hnat : (2672987891 : ℕ)^41*100000000000000^33 ≤ 45929755696081^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672987891 5000000000 45929755696081 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5335669299/10000000000 : ℝ), (-1342448917/10000000000 : ℝ), (2672987891/5000000000 : ℝ)] ![(4581976751821/10000000000000 : ℝ), (2062619194097/25000000000000 : ℝ), (45929755696081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5335669299/10000000000 : ℝ)|^41 ≤ (4581976751821/10000000000000 : ℝ)^33
        have hw : |(5335669299/10000000000 : ℝ)|=(5335669299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1342448917/10000000000 : ℝ)|^41 ≤ (2062619194097/25000000000000 : ℝ)^33
        have hw : |(-1342448917/10000000000 : ℝ)|=(1342448917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2672987891/5000000000 : ℝ)|^41 ≤ (45929755696081/100000000000000 : ℝ)^33
        have hw : |(2672987891/5000000000 : ℝ)|=(2672987891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321063_s2_s2_2 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (267344241/500000000 : ℝ)*x 0 + (2672006751/5000000000 : ℝ)*x 1 + (-1329501567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267344241/500000000 : ℝ)^41 ≤ (45939459188127/100000000000000 : ℝ)^33 := by
    have hnat : (267344241 : ℕ)^41*100000000000000^33 ≤ 45939459188127^33*500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267344241 500000000 45939459188127 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2672006751/5000000000 : ℝ)^41 ≤ (45908810775503/100000000000000 : ℝ)^33 := by
    have hnat : (2672006751 : ℕ)^41*100000000000000^33 ≤ 45908810775503^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672006751 5000000000 45908810775503 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1329501567/10000000000 : ℝ)^41 ≤ (1630346004189/20000000000000 : ℝ)^33 := by
    have hnat : (1329501567 : ℕ)^41*20000000000000^33 ≤ 1630346004189^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1329501567 10000000000 1630346004189 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267344241/500000000 : ℝ), (2672006751/5000000000 : ℝ), (-1329501567/10000000000 : ℝ)] ![(45939459188127/100000000000000 : ℝ), (45908810775503/100000000000000 : ℝ), (1630346004189/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267344241/500000000 : ℝ)|^41 ≤ (45939459188127/100000000000000 : ℝ)^33
        have hw : |(267344241/500000000 : ℝ)|=(267344241/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2672006751/5000000000 : ℝ)|^41 ≤ (45908810775503/100000000000000 : ℝ)^33
        have hw : |(2672006751/5000000000 : ℝ)|=(2672006751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1329501567/10000000000 : ℝ)|^41 ≤ (1630346004189/20000000000000 : ℝ)^33
        have hw : |(-1329501567/10000000000 : ℝ)|=(1329501567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321063_s2_s2_6 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (258397599/625000000 : ℝ)*x 0 + (2066316167/5000000000 : ℝ)*x 1 + (2061866181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (258397599/625000000 : ℝ)^41 ≤ (16687319133509/50000000000000 : ℝ)^33 := by
    have hnat : (258397599 : ℕ)^41*50000000000000^33 ≤ 16687319133509^33*625000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258397599 625000000 16687319133509 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2066316167/5000000000 : ℝ)^41 ≤ (667145913673/2000000000000 : ℝ)^33 := by
    have hnat : (2066316167 : ℕ)^41*2000000000000^33 ≤ 667145913673^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2066316167 5000000000 667145913673 2000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2061866181/5000000000 : ℝ)^41 ≤ (16634033018059/50000000000000 : ℝ)^33 := by
    have hnat : (2061866181 : ℕ)^41*50000000000000^33 ≤ 16634033018059^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061866181 5000000000 16634033018059 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(258397599/625000000 : ℝ), (2066316167/5000000000 : ℝ), (2061866181/5000000000 : ℝ)] ![(16687319133509/50000000000000 : ℝ), (667145913673/2000000000000 : ℝ), (16634033018059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(258397599/625000000 : ℝ)|^41 ≤ (16687319133509/50000000000000 : ℝ)^33
        have hw : |(258397599/625000000 : ℝ)|=(258397599/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2066316167/5000000000 : ℝ)|^41 ≤ (667145913673/2000000000000 : ℝ)^33
        have hw : |(2066316167/5000000000 : ℝ)|=(2066316167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2061866181/5000000000 : ℝ)|^41 ≤ (16634033018059/50000000000000 : ℝ)^33
        have hw : |(2061866181/5000000000 : ℝ)|=(2061866181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321063_s2_s2_7 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-316235463/2500000000 : ℝ)*x 0 + (4713646859/10000000000 : ℝ)*x 1 + (1200833337/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (316235463/2500000000 : ℝ)^41 ≤ (7662856595623/100000000000000 : ℝ)^33 := by
    have hnat : (316235463 : ℕ)^41*100000000000000^33 ≤ 7662856595623^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316235463 2500000000 7662856595623 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4713646859/10000000000 : ℝ)^41 ≤ (9819986251147/25000000000000 : ℝ)^33 := by
    have hnat : (4713646859 : ℕ)^41*25000000000000^33 ≤ 9819986251147^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4713646859 10000000000 9819986251147 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1200833337/2000000000 : ℝ)^41 ≤ (13264299594971/25000000000000 : ℝ)^33 := by
    have hnat : (1200833337 : ℕ)^41*25000000000000^33 ≤ 13264299594971^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1200833337 2000000000 13264299594971 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-316235463/2500000000 : ℝ), (4713646859/10000000000 : ℝ), (1200833337/2000000000 : ℝ)] ![(7662856595623/100000000000000 : ℝ), (9819986251147/25000000000000 : ℝ), (13264299594971/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-316235463/2500000000 : ℝ)|^41 ≤ (7662856595623/100000000000000 : ℝ)^33
        have hw : |(-316235463/2500000000 : ℝ)|=(316235463/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4713646859/10000000000 : ℝ)|^41 ≤ (9819986251147/25000000000000 : ℝ)^33
        have hw : |(4713646859/10000000000 : ℝ)|=(4713646859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1200833337/2000000000 : ℝ)|^41 ≤ (13264299594971/25000000000000 : ℝ)^33
        have hw : |(1200833337/2000000000 : ℝ)|=(1200833337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321063_s2_s2_8 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1269648551/2500000000 : ℝ)*x 0 + (-2929711/40000000 : ℝ)*x 1 + (1500202213/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1269648551/2500000000 : ℝ)^41 ≤ (21546593138517/50000000000000 : ℝ)^33 := by
    have hnat : (1269648551 : ℕ)^41*50000000000000^33 ≤ 21546593138517^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1269648551 2500000000 21546593138517 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2929711/40000000 : ℝ)^41 ≤ (971619591793/25000000000000 : ℝ)^33 := by
    have hnat : (2929711 : ℕ)^41*25000000000000^33 ≤ 971619591793^33*40000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2929711 40000000 971619591793 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1500202213/2500000000 : ℝ)^41 ≤ (1325508383517/2500000000000 : ℝ)^33 := by
    have hnat : (1500202213 : ℕ)^41*2500000000000^33 ≤ 1325508383517^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1500202213 2500000000 1325508383517 2500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1269648551/2500000000 : ℝ), (-2929711/40000000 : ℝ), (1500202213/2500000000 : ℝ)] ![(21546593138517/50000000000000 : ℝ), (971619591793/25000000000000 : ℝ), (1325508383517/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1269648551/2500000000 : ℝ)|^41 ≤ (21546593138517/50000000000000 : ℝ)^33
        have hw : |(1269648551/2500000000 : ℝ)|=(1269648551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2929711/40000000 : ℝ)|^41 ≤ (971619591793/25000000000000 : ℝ)^33
        have hw : |(-2929711/40000000 : ℝ)|=(2929711/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1500202213/2500000000 : ℝ)|^41 ≤ (1325508383517/2500000000000 : ℝ)^33
        have hw : |(1500202213/2500000000 : ℝ)|=(1500202213/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321063_s2_s2_9 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4888507469/10000000000 : ℝ)*x 0 + (774194161/1250000000 : ℝ)*x 1 + (-712758343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4888507469/10000000000 : ℝ)^41 ≤ (41098415543929/100000000000000 : ℝ)^33 := by
    have hnat : (4888507469 : ℕ)^41*100000000000000^33 ≤ 41098415543929^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4888507469 10000000000 41098415543929 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (774194161/1250000000 : ℝ)^41 ≤ (55144354982779/100000000000000 : ℝ)^33 := by
    have hnat : (774194161 : ℕ)^41*100000000000000^33 ≤ 55144354982779^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      774194161 1250000000 55144354982779 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (712758343/10000000000 : ℝ)^41 ≤ (375722945107/10000000000000 : ℝ)^33 := by
    have hnat : (712758343 : ℕ)^41*10000000000000^33 ≤ 375722945107^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      712758343 10000000000 375722945107 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4888507469/10000000000 : ℝ), (774194161/1250000000 : ℝ), (-712758343/10000000000 : ℝ)] ![(41098415543929/100000000000000 : ℝ), (55144354982779/100000000000000 : ℝ), (375722945107/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4888507469/10000000000 : ℝ)|^41 ≤ (41098415543929/100000000000000 : ℝ)^33
        have hw : |(4888507469/10000000000 : ℝ)|=(4888507469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(774194161/1250000000 : ℝ)|^41 ≤ (55144354982779/100000000000000 : ℝ)^33
        have hw : |(774194161/1250000000 : ℝ)|=(774194161/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-712758343/10000000000 : ℝ)|^41 ≤ (375722945107/10000000000000 : ℝ)^33
        have hw : |(-712758343/10000000000 : ℝ)|=(712758343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321063_s2_s2_13 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (4471769307/10000000000 : ℝ)*x 0 + (5397497631/10000000000 : ℝ)*x 1 + (1185607307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4471769307/10000000000 : ℝ)^41 ≤ (18395734214661/50000000000000 : ℝ)^33 := by
    have hnat : (4471769307 : ℕ)^41*50000000000000^33 ≤ 18395734214661^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4471769307 10000000000 18395734214661 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397497631/10000000000 : ℝ)^41 ≤ (5810044162401/12500000000000 : ℝ)^33 := by
    have hnat : (5397497631 : ℕ)^41*12500000000000^33 ≤ 5810044162401^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397497631 10000000000 5810044162401 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1185607307/5000000000 : ℝ)^41 ≤ (16728178262071/100000000000000 : ℝ)^33 := by
    have hnat : (1185607307 : ℕ)^41*100000000000000^33 ≤ 16728178262071^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1185607307 5000000000 16728178262071 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4471769307/10000000000 : ℝ), (5397497631/10000000000 : ℝ), (1185607307/5000000000 : ℝ)] ![(18395734214661/50000000000000 : ℝ), (5810044162401/12500000000000 : ℝ), (16728178262071/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4471769307/10000000000 : ℝ)|^41 ≤ (18395734214661/50000000000000 : ℝ)^33
        have hw : |(4471769307/10000000000 : ℝ)|=(4471769307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397497631/10000000000 : ℝ)|^41 ≤ (5810044162401/12500000000000 : ℝ)^33
        have hw : |(5397497631/10000000000 : ℝ)|=(5397497631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1185607307/5000000000 : ℝ)|^41 ≤ (16728178262071/100000000000000 : ℝ)^33
        have hw : |(1185607307/5000000000 : ℝ)|=(1185607307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321063_s2_s2_14 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-366512547/5000000000 : ℝ)*x 0 + (508598127/1000000000 : ℝ)*x 1 + (1498338371/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (366512547/5000000000 : ℝ)^41 ≤ (486302106083/12500000000000 : ℝ)^33 := by
    have hnat : (366512547 : ℕ)^41*12500000000000^33 ≤ 486302106083^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366512547 5000000000 486302106083 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (508598127/1000000000 : ℝ)^41 ≤ (5396384575463/12500000000000 : ℝ)^33 := by
    have hnat : (508598127 : ℕ)^41*12500000000000^33 ≤ 5396384575463^33*1000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508598127 1000000000 5396384575463 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1498338371/2500000000 : ℝ)^41 ≤ (5293850652757/10000000000000 : ℝ)^33 := by
    have hnat : (1498338371 : ℕ)^41*10000000000000^33 ≤ 5293850652757^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1498338371 2500000000 5293850652757 10000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-366512547/5000000000 : ℝ), (508598127/1000000000 : ℝ), (1498338371/2500000000 : ℝ)] ![(486302106083/12500000000000 : ℝ), (5396384575463/12500000000000 : ℝ), (5293850652757/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-366512547/5000000000 : ℝ)|^41 ≤ (486302106083/12500000000000 : ℝ)^33
        have hw : |(-366512547/5000000000 : ℝ)|=(366512547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(508598127/1000000000 : ℝ)|^41 ≤ (5396384575463/12500000000000 : ℝ)^33
        have hw : |(508598127/1000000000 : ℝ)|=(508598127/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1498338371/2500000000 : ℝ)|^41 ≤ (5293850652757/10000000000000 : ℝ)^33
        have hw : |(1498338371/2500000000 : ℝ)|=(1498338371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321063_s2_s2_15 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (1182697383/2500000000 : ℝ)*x 0 + (-1262013101/10000000000 : ℝ)*x 1 + (5989996769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1182697383/2500000000 : ℝ)^41 ≤ (19728754215533/50000000000000 : ℝ)^33 := by
    have hnat : (1182697383 : ℕ)^41*50000000000000^33 ≤ 19728754215533^33*2500000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1182697383 2500000000 19728754215533 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1262013101/10000000000 : ℝ)^41 ≤ (3820409847029/50000000000000 : ℝ)^33 := by
    have hnat : (1262013101 : ℕ)^41*50000000000000^33 ≤ 3820409847029^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1262013101 10000000000 3820409847029 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5989996769/10000000000 : ℝ)^41 ≤ (10580334373099/20000000000000 : ℝ)^33 := by
    have hnat : (5989996769 : ℕ)^41*20000000000000^33 ≤ 10580334373099^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5989996769 10000000000 10580334373099 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1182697383/2500000000 : ℝ), (-1262013101/10000000000 : ℝ), (5989996769/10000000000 : ℝ)] ![(19728754215533/50000000000000 : ℝ), (3820409847029/50000000000000 : ℝ), (10580334373099/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1182697383/2500000000 : ℝ)|^41 ≤ (19728754215533/50000000000000 : ℝ)^33
        have hw : |(1182697383/2500000000 : ℝ)|=(1182697383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1262013101/10000000000 : ℝ)|^41 ≤ (3820409847029/50000000000000 : ℝ)^33
        have hw : |(-1262013101/10000000000 : ℝ)|=(1262013101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5989996769/10000000000 : ℝ)|^41 ≤ (10580334373099/20000000000000 : ℝ)^33
        have hw : |(5989996769/10000000000 : ℝ)|=(5989996769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321063_s2_s2_16 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (5990582859/10000000000 : ℝ)*x 0 + (5094764629/10000000000 : ℝ)*x 1 + (-361785283/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5990582859/10000000000 : ℝ)^41 ≤ (26454051459983/50000000000000 : ℝ)^33 := by
    have hnat : (5990582859 : ℕ)^41*50000000000000^33 ≤ 26454051459983^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5990582859 10000000000 26454051459983 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5094764629/10000000000 : ℝ)^41 ≤ (43263725347541/100000000000000 : ℝ)^33 := by
    have hnat : (5094764629 : ℕ)^41*100000000000000^33 ≤ 43263725347541^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5094764629 10000000000 43263725347541 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (361785283/5000000000 : ℝ)^41 ≤ (3828171724983/100000000000000 : ℝ)^33 := by
    have hnat : (361785283 : ℕ)^41*100000000000000^33 ≤ 3828171724983^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      361785283 5000000000 3828171724983 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5990582859/10000000000 : ℝ), (5094764629/10000000000 : ℝ), (-361785283/5000000000 : ℝ)] ![(26454051459983/50000000000000 : ℝ), (43263725347541/100000000000000 : ℝ), (3828171724983/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5990582859/10000000000 : ℝ)|^41 ≤ (26454051459983/50000000000000 : ℝ)^33
        have hw : |(5990582859/10000000000 : ℝ)|=(5990582859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5094764629/10000000000 : ℝ)|^41 ≤ (43263725347541/100000000000000 : ℝ)^33
        have hw : |(5094764629/10000000000 : ℝ)|=(5094764629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-361785283/5000000000 : ℝ)|^41 ≤ (3828171724983/100000000000000 : ℝ)^33
        have hw : |(-361785283/5000000000 : ℝ)|=(361785283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321063_s2_s2_20 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (2958723807/5000000000 : ℝ)*x 0 + (1942821879/5000000000 : ℝ)*x 1 + (300195661/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2958723807/5000000000 : ℝ)^41 ≤ (10421357091631/20000000000000 : ℝ)^33 := by
    have hnat : (2958723807 : ℕ)^41*20000000000000^33 ≤ 10421357091631^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2958723807 5000000000 10421357091631 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1942821879/5000000000 : ℝ)^41 ≤ (1235944151751/4000000000000 : ℝ)^33 := by
    have hnat : (1942821879 : ℕ)^41*4000000000000^33 ≤ 1235944151751^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1942821879 5000000000 1235944151751 4000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (300195661/1250000000 : ℝ)^41 ≤ (16994610732883/100000000000000 : ℝ)^33 := by
    have hnat : (300195661 : ℕ)^41*100000000000000^33 ≤ 16994610732883^33*1250000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300195661 1250000000 16994610732883 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2958723807/5000000000 : ℝ), (1942821879/5000000000 : ℝ), (300195661/1250000000 : ℝ)] ![(10421357091631/20000000000000 : ℝ), (1235944151751/4000000000000 : ℝ), (16994610732883/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2958723807/5000000000 : ℝ)|^41 ≤ (10421357091631/20000000000000 : ℝ)^33
        have hw : |(2958723807/5000000000 : ℝ)|=(2958723807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1942821879/5000000000 : ℝ)|^41 ≤ (1235944151751/4000000000000 : ℝ)^33
        have hw : |(1942821879/5000000000 : ℝ)|=(1942821879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(300195661/1250000000 : ℝ)|^41 ≤ (16994610732883/100000000000000 : ℝ)^33
        have hw : |(300195661/1250000000 : ℝ)|=(300195661/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321063_s2_s2_21 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (-340772591/5000000000 : ℝ)*x 0 + (2861377091/5000000000 : ℝ)*x 1 + (2697832811/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (340772591/5000000000 : ℝ)^41 ≤ (1776951118347/50000000000000 : ℝ)^33 := by
    have hnat : (340772591 : ℕ)^41*50000000000000^33 ≤ 1776951118347^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340772591 5000000000 1776951118347 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2861377091/5000000000 : ℝ)^41 ≤ (12496336116563/25000000000000 : ℝ)^33 := by
    have hnat : (2861377091 : ℕ)^41*25000000000000^33 ≤ 12496336116563^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2861377091 5000000000 12496336116563 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697832811/5000000000 : ℝ)^41 ≤ (11615188318721/25000000000000 : ℝ)^33 := by
    have hnat : (2697832811 : ℕ)^41*25000000000000^33 ≤ 11615188318721^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697832811 5000000000 11615188318721 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-340772591/5000000000 : ℝ), (2861377091/5000000000 : ℝ), (2697832811/5000000000 : ℝ)] ![(1776951118347/50000000000000 : ℝ), (12496336116563/25000000000000 : ℝ), (11615188318721/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-340772591/5000000000 : ℝ)|^41 ≤ (1776951118347/50000000000000 : ℝ)^33
        have hw : |(-340772591/5000000000 : ℝ)|=(340772591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2861377091/5000000000 : ℝ)|^41 ≤ (12496336116563/25000000000000 : ℝ)^33
        have hw : |(2861377091/5000000000 : ℝ)|=(2861377091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697832811/5000000000 : ℝ)|^41 ≤ (11615188318721/25000000000000 : ℝ)^33
        have hw : |(2697832811/5000000000 : ℝ)|=(2697832811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321063_s2_s2_22 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (3015340803/5000000000 : ℝ)*x 0 + (-680392381/10000000000 : ℝ)*x 1 + (5079724667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3015340803/5000000000 : ℝ)^41 ≤ (53348460480609/100000000000000 : ℝ)^33 := by
    have hnat : (3015340803 : ℕ)^41*100000000000000^33 ≤ 53348460480609^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3015340803 5000000000 53348460480609 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (680392381/10000000000 : ℝ)^41 ≤ (886608809833/25000000000000 : ℝ)^33 := by
    have hnat : (680392381 : ℕ)^41*25000000000000^33 ≤ 886608809833^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680392381 10000000000 886608809833 25000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5079724667/10000000000 : ℝ)^41 ≤ (43105104268777/100000000000000 : ℝ)^33 := by
    have hnat : (5079724667 : ℕ)^41*100000000000000^33 ≤ 43105104268777^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5079724667 10000000000 43105104268777 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3015340803/5000000000 : ℝ), (-680392381/10000000000 : ℝ), (5079724667/10000000000 : ℝ)] ![(53348460480609/100000000000000 : ℝ), (886608809833/25000000000000 : ℝ), (43105104268777/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3015340803/5000000000 : ℝ)|^41 ≤ (53348460480609/100000000000000 : ℝ)^33
        have hw : |(3015340803/5000000000 : ℝ)|=(3015340803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-680392381/10000000000 : ℝ)|^41 ≤ (886608809833/25000000000000 : ℝ)^33
        have hw : |(-680392381/10000000000 : ℝ)|=(680392381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5079724667/10000000000 : ℝ)|^41 ≤ (43105104268777/100000000000000 : ℝ)^33
        have hw : |(5079724667/10000000000 : ℝ)|=(5079724667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321063_s2_s2_23 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (37457129/80000000 : ℝ)*x 0 + (3022057287/5000000000 : ℝ)*x 1 + (-249980951/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (37457129/80000000 : ℝ)^41 ≤ (7790803538619/20000000000000 : ℝ)^33 := by
    have hnat : (37457129 : ℕ)^41*20000000000000^33 ≤ 7790803538619^33*80000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37457129 80000000 7790803538619 20000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3022057287/5000000000 : ℝ)^41 ≤ (1671754314347/3125000000000 : ℝ)^33 := by
    have hnat : (3022057287 : ℕ)^41*3125000000000^33 ≤ 1671754314347^33*5000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3022057287 5000000000 1671754314347 3125000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (249980951/2000000000 : ℝ)^41 ≤ (7549844239639/100000000000000 : ℝ)^33 := by
    have hnat : (249980951 : ℕ)^41*100000000000000^33 ≤ 7549844239639^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249980951 2000000000 7549844239639 100000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(37457129/80000000 : ℝ), (3022057287/5000000000 : ℝ), (-249980951/2000000000 : ℝ)] ![(7790803538619/20000000000000 : ℝ), (1671754314347/3125000000000 : ℝ), (7549844239639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(37457129/80000000 : ℝ)|^41 ≤ (7790803538619/20000000000000 : ℝ)^33
        have hw : |(37457129/80000000 : ℝ)|=(37457129/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3022057287/5000000000 : ℝ)|^41 ≤ (1671754314347/3125000000000 : ℝ)^33
        have hw : |(3022057287/5000000000 : ℝ)|=(3022057287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-249980951/2000000000 : ℝ)|^41 ≤ (7549844239639/100000000000000 : ℝ)^33
        have hw : |(-249980951/2000000000 : ℝ)|=(249980951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c321063_s2_s2_27 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ)) (x : Fin 3 → ℝ) :
    (6085974619/10000000000 : ℝ)*x 0 + (626085529/2000000000 : ℝ)*x 1 + (600317719/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6085974619/10000000000 : ℝ)^41 ≤ (1686151352903/3125000000000 : ℝ)^33 := by
    have hnat : (6085974619 : ℕ)^41*3125000000000^33 ≤ 1686151352903^33*10000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6085974619 10000000000 1686151352903 3125000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (626085529/2000000000 : ℝ)^41 ≤ (11811247671823/50000000000000 : ℝ)^33 := by
    have hnat : (626085529 : ℕ)^41*50000000000000^33 ≤ 11811247671823^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626085529 2000000000 11811247671823 50000000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (600317719/2000000000 : ℝ)^41 ≤ (2802582669031/12500000000000 : ℝ)^33 := by
    have hnat : (600317719 : ℕ)^41*12500000000000^33 ≤ 2802582669031^33*2000000000^41 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600317719 2000000000 2802582669031 12500000000000 41 33 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (41/8 : ℝ)) 41 33 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6085974619/10000000000 : ℝ), (626085529/2000000000 : ℝ), (600317719/2000000000 : ℝ)] ![(1686151352903/3125000000000 : ℝ), (11811247671823/50000000000000 : ℝ), (2802582669031/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6085974619/10000000000 : ℝ)|^41 ≤ (1686151352903/3125000000000 : ℝ)^33
        have hw : |(6085974619/10000000000 : ℝ)|=(6085974619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(626085529/2000000000 : ℝ)|^41 ≤ (11811247671823/50000000000000 : ℝ)^33
        have hw : |(626085529/2000000000 : ℝ)|=(626085529/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(600317719/2000000000 : ℝ)|^41 ≤ (2802582669031/12500000000000 : ℝ)^33
        have hw : |(600317719/2000000000 : ℝ)|=(600317719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c321063_s2 (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((9537/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9537/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12077/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(12077/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11547/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(11547/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((29039/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29039/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29457/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29457/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28233/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(28233/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (80491/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (80491/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (80491/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (80491/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80491/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80491/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (9537/20000 : ℝ) ^ (81/16 : ℝ) ≤ (294250906564784843/12500000000000000000 : ℝ) := by
    have hpowers : (9537/20000 : ℝ)^81 ≤ (294250906564784843/12500000000000000000 : ℝ)^16 := by
      have hnat : (9537 : ℕ)^81*12500000000000000000^16 ≤ 294250906564784843^16*20000^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9537 20000 294250906564784843 12500000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9537/20000 : ℝ)) (X := (294250906564784843/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s2_corner0a : (12794250906564784843/12500000000000000000 : ℝ) ≤ (2511516458306907/2500000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (12794250906564784843/12500000000000000000 : ℝ)^16 ≤ (2511516458306907/2500000000000000 : ℝ)^81 := by
      have hnat : (12794250906564784843 : ℕ)^16*2500000000000000^81 ≤ 2511516458306907^81*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12794250906564784843 12500000000000000000 2511516458306907 2500000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2511516458306907/2500000000000000 : ℝ)) (X := (12794250906564784843/12500000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s2_corner0b : (6544250906564784843/6250000000000000000 : ℝ) ≤ (2522822295482677/2500000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (6544250906564784843/6250000000000000000 : ℝ)^16 ≤ (2522822295482677/2500000000000000 : ℝ)^81 := by
      have hnat : (6544250906564784843 : ℕ)^16*2500000000000000^81 ≤ 2522822295482677^81*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6544250906564784843 6250000000000000000 2522822295482677 2500000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2522822295482677/2500000000000000 : ℝ)) (X := (6544250906564784843/6250000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(11516458306907/1192125000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(1130583717577/119212500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (9537/20000 : ℝ)) (alpha := (11516458306907/1192125000000000 : ℝ)) (beta := (1130583717577/119212500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (9537/20000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(11516458306907/1192125000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(1130583717577/119212500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (12077/25000 : ℝ) ^ (81/16 : ℝ) ≤ (2513891208933059727/100000000000000000000 : ℝ) := by
    have hpowers : (12077/25000 : ℝ)^81 ≤ (2513891208933059727/100000000000000000000 : ℝ)^16 := by
      have hnat : (12077 : ℕ)^81*100000000000000000000^16 ≤ 2513891208933059727^16*25000^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12077 25000 2513891208933059727 100000000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12077/25000 : ℝ)) (X := (2513891208933059727/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s2_corner1a : (102513891208933059727/100000000000000000000 : ℝ) ≤ (2512290918324839/2500000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (102513891208933059727/100000000000000000000 : ℝ)^16 ≤ (2512290918324839/2500000000000000 : ℝ)^81 := by
      have hnat : (102513891208933059727 : ℕ)^16*2500000000000000^81 ≤ 2512290918324839^81*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102513891208933059727 100000000000000000000 2512290918324839 2500000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2512290918324839/2500000000000000 : ℝ)) (X := (102513891208933059727/100000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s2_corner1b : (52513891208933059727/50000000000000000000 : ℝ) ≤ (5048684601387439/5000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (52513891208933059727/50000000000000000000 : ℝ)^16 ≤ (5048684601387439/5000000000000000 : ℝ)^81 := by
      have hnat : (52513891208933059727 : ℕ)^16*5000000000000000^81 ≤ 5048684601387439^81*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52513891208933059727 50000000000000000000 5048684601387439 5000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5048684601387439/5000000000000000 : ℝ)) (X := (52513891208933059727/50000000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(12290918324839/1207700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(24102764737761/2415400000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (12077/25000 : ℝ)) (alpha := (12290918324839/1207700000000000 : ℝ)) (beta := (24102764737761/2415400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (12077/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(12290918324839/1207700000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(24102764737761/2415400000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (11547/25000 : ℝ) ^ (81/16 : ℝ) ≤ (250373794370499017/12500000000000000000 : ℝ) := by
    have hpowers : (11547/25000 : ℝ)^81 ≤ (250373794370499017/12500000000000000000 : ℝ)^16 := by
      have hnat : (11547 : ℕ)^81*12500000000000000000^16 ≤ 250373794370499017^16*25000^81 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11547 25000 250373794370499017 12500000000000000000 81 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11547/25000 : ℝ)) (X := (250373794370499017/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s2_corner2a : (12750373794370499017/12500000000000000000 : ℝ) ≤ (2509812760436249/2500000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (12750373794370499017/12500000000000000000 : ℝ)^16 ≤ (2509812760436249/2500000000000000 : ℝ)^81 := by
      have hnat : (12750373794370499017 : ℕ)^16*2500000000000000^81 ≤ 2509812760436249^81*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12750373794370499017 12500000000000000000 2509812760436249 2500000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2509812760436249/2500000000000000 : ℝ)) (X := (12750373794370499017/12500000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have s2_corner2b : (6500373794370499017/6250000000000000000 : ℝ) ≤ (5038944184040441/5000000000000000 : ℝ) ^ (81/16 : ℝ) := by
    have hpowers : (6500373794370499017/6250000000000000000 : ℝ)^16 ≤ (5038944184040441/5000000000000000 : ℝ)^81 := by
      have hnat : (6500373794370499017 : ℕ)^16*5000000000000000^81 ≤ 5038944184040441^81*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6500373794370499017 6250000000000000000 5038944184040441 5000000000000000 16 81 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5038944184040441/5000000000000000 : ℝ)) (X := (6500373794370499017/6250000000000000000 : ℝ)) (by norm_num) 81 16 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(9812760436249/1154700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(19318663167943/2309400000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (81/16 : ℝ)) (rho := (11547/25000 : ℝ)) (alpha := (9812760436249/1154700000000000 : ℝ)) (beta := (19318663167943/2309400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (11547/25000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(9812760436249/1154700000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(19318663167943/2309400000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-1338470937/10000000000 : ℝ)*X 0 0+(2667587993/5000000000 : ℝ)*X 0 1+(2674656601/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321063_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((5335669299/10000000000 : ℝ)*X 1 0+(-1342448917/10000000000 : ℝ)*X 1 1+(2672987891/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321063_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((267344241/500000000 : ℝ)*X 2 0+(2672006751/5000000000 : ℝ)*X 2 1+(-1329501567/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321063_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((258397599/625000000 : ℝ)*X 0 0+(2066316167/5000000000 : ℝ)*X 0 1+(2061866181/5000000000 : ℝ)*X 0 2+(258397599/625000000 : ℝ)*X 1 0+(2066316167/5000000000 : ℝ)*X 1 1+(2061866181/5000000000 : ℝ)*X 1 2+(258397599/625000000 : ℝ)*X 2 0+(2066316167/5000000000 : ℝ)*X 2 1+(2061866181/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321063_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-316235463/2500000000 : ℝ)*X 0 0+(4713646859/10000000000 : ℝ)*X 0 1+(1200833337/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321063_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((1269648551/2500000000 : ℝ)*X 1 0+(-2929711/40000000 : ℝ)*X 1 1+(1500202213/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321063_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((4888507469/10000000000 : ℝ)*X 2 0+(774194161/1250000000 : ℝ)*X 2 1+(-712758343/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321063_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((4471769307/10000000000 : ℝ)*X 0 0+(5397497631/10000000000 : ℝ)*X 0 1+(1185607307/5000000000 : ℝ)*X 0 2+(4471769307/10000000000 : ℝ)*X 1 0+(5397497631/10000000000 : ℝ)*X 1 1+(1185607307/5000000000 : ℝ)*X 1 2+(4471769307/10000000000 : ℝ)*X 2 0+(5397497631/10000000000 : ℝ)*X 2 1+(1185607307/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321063_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-366512547/5000000000 : ℝ)*X 0 0+(508598127/1000000000 : ℝ)*X 0 1+(1498338371/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321063_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((1182697383/2500000000 : ℝ)*X 1 0+(-1262013101/10000000000 : ℝ)*X 1 1+(5989996769/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321063_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((5990582859/10000000000 : ℝ)*X 2 0+(5094764629/10000000000 : ℝ)*X 2 1+(-361785283/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321063_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((2958723807/5000000000 : ℝ)*X 0 0+(1942821879/5000000000 : ℝ)*X 0 1+(300195661/1250000000 : ℝ)*X 0 2+(2958723807/5000000000 : ℝ)*X 1 0+(1942821879/5000000000 : ℝ)*X 1 1+(300195661/1250000000 : ℝ)*X 1 2+(2958723807/5000000000 : ℝ)*X 2 0+(1942821879/5000000000 : ℝ)*X 2 1+(300195661/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321063_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-340772591/5000000000 : ℝ)*X 0 0+(2861377091/5000000000 : ℝ)*X 0 1+(2697832811/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c321063_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((3015340803/5000000000 : ℝ)*X 1 0+(-680392381/10000000000 : ℝ)*X 1 1+(5079724667/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c321063_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((37457129/80000000 : ℝ)*X 2 0+(3022057287/5000000000 : ℝ)*X 2 1+(-249980951/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c321063_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((6085974619/10000000000 : ℝ)*X 0 0+(626085529/2000000000 : ℝ)*X 0 1+(600317719/2000000000 : ℝ)*X 0 2+(6085974619/10000000000 : ℝ)*X 1 0+(626085529/2000000000 : ℝ)*X 1 1+(600317719/2000000000 : ℝ)*X 1 2+(6085974619/10000000000 : ℝ)*X 2 0+(626085529/2000000000 : ℝ)*X 2 1+(600317719/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c321063_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((29039/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29039/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (60075129980012155722577524393/6157242573625000000000000000000000 : ℝ) := by norm_num
    linear_combination (271401/250000000000 : ℝ)*(base50) + (158684081989/1000000000000 : ℝ)*(base60) + (333815479993/62500000000 : ℝ)*(major_s2_0) + (333815479993/62500000000 : ℝ)*(major_s2_1) + (333815479993/62500000000 : ℝ)*(major_s2_2) + (908229/31250000000 : ℝ)*(sp_s2_0) + (1209261/100000000000 : ℝ)*(sp_s2_6) + (7876152938779/1000000000000 : ℝ)*(sp_s2_7) + (787614342971/100000000000 : ℝ)*(sp_s2_8) + (1575229958789/200000000000 : ℝ)*(sp_s2_9) + (1402933686371/500000000000 : ℝ)*(sp_s2_13) + (7660009/250000000000 : ℝ)*(sp_s2_14) + (69212433/1000000000000 : ℝ)*(sp_s2_15) + (62848197/1000000000000 : ℝ)*(sp_s2_23) + (2805879465353/1000000000000 : ℝ)*(f.failure) + (7876212642143/1000000000000 : ℝ)*(f.sum) + (49008425230489247/3486327975000000000000000000000 : ℝ)*base63 + (165113209590811/577350000000000000000000000 : ℝ)*base65 + (172857075237037/603850000000000000000000000 : ℝ)*base67 + (20611280045503/288675000000000000000000000 : ℝ)*base69 + (3268398466144760863/9176978250000000000000000000000 : ℝ)*base71 + (60762928591579/476850000000000000000000000 : ℝ)*base73 + (38876494674547/75481250000000000000000000 : ℝ)*base75 + (441296870526583/596062500000000000000000000 : ℝ)*base77 + (891879841894878301/2879458725000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (4641/6250000000000000 : ℝ)*base87 + (4641/6250000000000000 : ℝ)*base89 + (4641/6250000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29457/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29457/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (11502356149045108380678763/764748187500000000000000000000 : ℝ) := by norm_num
    linear_combination (3973593/1000000000000 : ℝ)*(base60) + (2715976104263/500000000000 : ℝ)*(major_s2_0) + (2715976104263/500000000000 : ℝ)*(major_s2_1) + (2715976104263/500000000000 : ℝ)*(major_s2_2) + (44264561/1000000000000 : ℝ)*(sp_s2_0) + (57253/1250000000 : ℝ)*(sp_s2_1) + (32611/320000000 : ℝ)*(sp_s2_2) + (63900143/1000000000000 : ℝ)*(sp_s2_7) + (28233937/500000000000 : ℝ)*(sp_s2_8) + (4005077879483/500000000000 : ℝ)*(sp_s2_14) + (1602032330679/200000000000 : ℝ)*(sp_s2_15) + (1602032402859/200000000000 : ℝ)*(sp_s2_16) + (35669239491/12500000000 : ℝ)*(sp_s2_20) + (96320529/1000000000000 : ℝ)*(sp_s2_27) + (2853635479809/1000000000000 : ℝ)*(f.failure) + (801026392367/100000000000 : ℝ)*(f.sum) + (17721873797683303/435790996875000000000000000000 : ℝ)*base63 + (285612072455551/1154700000000000000000000000 : ℝ)*base64 + (388880888101177/1207700000000000000000000000 : ℝ)*base66 + (73119703505671/288675000000000000000000000 : ℝ)*base69 + (845576882839467973/18353956500000000000000000000000 : ℝ)*base70 + (67698171342689/238425000000000000000000000 : ℝ)*base73 + (181274120657603/603850000000000000000000000 : ℝ)*base74 + (310764873301543/1192125000000000000000000000 : ℝ)*base76 + (314247231551594023/11517834900000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (173/6250000000000000 : ℝ)*base87 + (173/6250000000000000 : ℝ)*base89 + (173/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28233/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(28233/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (16514761558811604744179142299/985158811780000000000000000000000 : ℝ) := by norm_num
    linear_combination (802239/500000000000 : ℝ)*(base15) + (229853571401/1000000000000 : ℝ)*(base40) + (4986514418187/1000000000000 : ℝ)*(major_s2_0) + (4986514418187/1000000000000 : ℝ)*(major_s2_1) + (4986514418187/1000000000000 : ℝ)*(major_s2_2) + (21823937/250000000000 : ℝ)*(sp_s2_0) + (10727001/125000000000 : ℝ)*(sp_s2_1) + (3112053/200000000000 : ℝ)*(sp_s2_2) + (1859/31250000 : ℝ)*(sp_s2_9) + (108962483/1000000000000 : ℝ)*(sp_s2_20) + (3676653942861/500000000000 : ℝ)*(sp_s2_21) + (919163470123/125000000000 : ℝ)*(sp_s2_22) + (3676660066603/500000000000 : ℝ)*(sp_s2_23) + (523903820913/200000000000 : ℝ)*(sp_s2_27) + (327453508381/125000000000 : ℝ)*(f.failure) + (7353395181471/1000000000000 : ℝ)*(f.sum) + (435221578056277/145263665625000000000000000000 : ℝ)*base63 + (25551245191133/769800000000000000000000000 : ℝ)*base64 + (149410364407553/2415400000000000000000000000 : ℝ)*base66 + (19036021822951/384900000000000000000000000 : ℝ)*base69 + (3045161218683680941/12235971000000000000000000000000 : ℝ)*base71 + (64722850106853/158950000000000000000000000 : ℝ)*base72 + (675674709650297/1207700000000000000000000000 : ℝ)*base74 + (280548610534769/794750000000000000000000000 : ℝ)*base76 + (1604441426772739231/7678556600000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (653/3125000000000000 : ℝ)*base87 + (653/3125000000000000 : ℝ)*base89 + (653/3125000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (81/16 : ℝ) ≤ p) (hpb : p ≤ (41/8 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (11897/6250 : ℝ) (168549/100000 : ℝ) (80491/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((9537/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(9537/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(12077/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(12077/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(11547/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(11547/25000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((29039/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(29039/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(29457/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(29457/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(28233/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(28233/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c321063_s2 p hpa hpb X hX hprev1

#print axioms solution
