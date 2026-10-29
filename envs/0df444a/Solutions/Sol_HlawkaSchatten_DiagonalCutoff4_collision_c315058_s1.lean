-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c315058_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:55:59.737029+00:00
-- url     : https://prove2.me/submissions/6befefad-bdf3-4ec4-95de-ce0090bb74eb

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
theorem collision_support_c315058_s1_s1_0 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-212175587/625000000 : ℝ)*x 0 + (1665797771/5000000000 : ℝ)*x 1 + (-1439473073/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212175587/625000000 : ℝ)^19 ≤ (6362671610039/25000000000000 : ℝ)^15 := by
    have hnat : (212175587 : ℕ)^19*25000000000000^15 ≤ 6362671610039^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212175587 625000000 6362671610039 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1665797771/5000000000 : ℝ)^19 ≤ (24851896994601/100000000000000 : ℝ)^15 := by
    have hnat : (1665797771 : ℕ)^19*100000000000000^15 ≤ 24851896994601^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1665797771 5000000000 24851896994601 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1439473073/2500000000 : ℝ)^19 ≤ (776522133491/1562500000000 : ℝ)^15 := by
    have hnat : (1439473073 : ℕ)^19*1562500000000^15 ≤ 776522133491^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1439473073 2500000000 776522133491 1562500000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-212175587/625000000 : ℝ), (1665797771/5000000000 : ℝ), (-1439473073/2500000000 : ℝ)] ![(6362671610039/25000000000000 : ℝ), (24851896994601/100000000000000 : ℝ), (776522133491/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-212175587/625000000 : ℝ)|^19 ≤ (6362671610039/25000000000000 : ℝ)^15
        have hw : |(-212175587/625000000 : ℝ)|=(212175587/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1665797771/5000000000 : ℝ)|^19 ≤ (24851896994601/100000000000000 : ℝ)^15
        have hw : |(1665797771/5000000000 : ℝ)|=(1665797771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1439473073/2500000000 : ℝ)|^19 ≤ (776522133491/1562500000000 : ℝ)^15
        have hw : |(-1439473073/2500000000 : ℝ)|=(1439473073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315058_s1_s1_1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (62475033/200000000 : ℝ)*x 0 + (-23915421/78125000 : ℝ)*x 1 + (-1554277663/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (62475033/200000000 : ℝ)^19 ≤ (4580928997811/20000000000000 : ℝ)^15 := by
    have hnat : (62475033 : ℕ)^19*20000000000000^15 ≤ 4580928997811^15*200000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62475033 200000000 4580928997811 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (23915421/78125000 : ℝ)^19 ≤ (22324999961523/100000000000000 : ℝ)^15 := by
    have hnat : (23915421 : ℕ)^19*100000000000000^15 ≤ 22324999961523^15*78125000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      23915421 78125000 22324999961523 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1554277663/2500000000 : ℝ)^19 ≤ (54770355042391/100000000000000 : ℝ)^15 := by
    have hnat : (1554277663 : ℕ)^19*100000000000000^15 ≤ 54770355042391^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1554277663 2500000000 54770355042391 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(62475033/200000000 : ℝ), (-23915421/78125000 : ℝ), (-1554277663/2500000000 : ℝ)] ![(4580928997811/20000000000000 : ℝ), (22324999961523/100000000000000 : ℝ), (54770355042391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(62475033/200000000 : ℝ)|^19 ≤ (4580928997811/20000000000000 : ℝ)^15
        have hw : |(62475033/200000000 : ℝ)|=(62475033/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-23915421/78125000 : ℝ)|^19 ≤ (22324999961523/100000000000000 : ℝ)^15
        have hw : |(-23915421/78125000 : ℝ)|=(23915421/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1554277663/2500000000 : ℝ)|^19 ≤ (54770355042391/100000000000000 : ℝ)^15
        have hw : |(-1554277663/2500000000 : ℝ)|=(1554277663/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315058_s1_s1_2 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (684390881/1250000000 : ℝ)*x 0 + (2640939681/5000000000 : ℝ)*x 1 + (183844807/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (684390881/1250000000 : ℝ)^19 ≤ (23313241324229/50000000000000 : ℝ)^15 := by
    have hnat : (684390881 : ℕ)^19*50000000000000^15 ≤ 23313241324229^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      684390881 1250000000 23313241324229 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2640939681/5000000000 : ℝ)^19 ≤ (44551815369921/100000000000000 : ℝ)^15 := by
    have hnat : (2640939681 : ℕ)^19*100000000000000^15 ≤ 44551815369921^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2640939681 5000000000 44551815369921 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (183844807/1250000000 : ℝ)^19 ≤ (4410850986401/50000000000000 : ℝ)^15 := by
    have hnat : (183844807 : ℕ)^19*50000000000000^15 ≤ 4410850986401^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      183844807 1250000000 4410850986401 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(684390881/1250000000 : ℝ), (2640939681/5000000000 : ℝ), (183844807/1250000000 : ℝ)] ![(23313241324229/50000000000000 : ℝ), (44551815369921/100000000000000 : ℝ), (4410850986401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(684390881/1250000000 : ℝ)|^19 ≤ (23313241324229/50000000000000 : ℝ)^15
        have hw : |(684390881/1250000000 : ℝ)|=(684390881/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2640939681/5000000000 : ℝ)|^19 ≤ (44551815369921/100000000000000 : ℝ)^15
        have hw : |(2640939681/5000000000 : ℝ)|=(2640939681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(183844807/1250000000 : ℝ)|^19 ≤ (4410850986401/50000000000000 : ℝ)^15
        have hw : |(183844807/1250000000 : ℝ)|=(183844807/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315058_s1_s1_6 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4635464587/10000000000 : ℝ)*x 0 + (775493363/1250000000 : ℝ)*x 1 + (-1309480027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4635464587/10000000000 : ℝ)^19 ≤ (37761694318017/100000000000000 : ℝ)^15 := by
    have hnat : (4635464587 : ℕ)^19*100000000000000^15 ≤ 37761694318017^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4635464587 10000000000 37761694318017 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (775493363/1250000000 : ℝ)^19 ≤ (54623504290871/100000000000000 : ℝ)^15 := by
    have hnat : (775493363 : ℕ)^19*100000000000000^15 ≤ 54623504290871^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      775493363 1250000000 54623504290871 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1309480027/10000000000 : ℝ)^19 ≤ (7614801375227/100000000000000 : ℝ)^15 := by
    have hnat : (1309480027 : ℕ)^19*100000000000000^15 ≤ 7614801375227^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309480027 10000000000 7614801375227 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4635464587/10000000000 : ℝ), (775493363/1250000000 : ℝ), (-1309480027/10000000000 : ℝ)] ![(37761694318017/100000000000000 : ℝ), (54623504290871/100000000000000 : ℝ), (7614801375227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4635464587/10000000000 : ℝ)|^19 ≤ (37761694318017/100000000000000 : ℝ)^15
        have hw : |(4635464587/10000000000 : ℝ)|=(4635464587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(775493363/1250000000 : ℝ)|^19 ≤ (54623504290871/100000000000000 : ℝ)^15
        have hw : |(775493363/1250000000 : ℝ)|=(775493363/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1309480027/10000000000 : ℝ)|^19 ≤ (7614801375227/100000000000000 : ℝ)^15
        have hw : |(-1309480027/10000000000 : ℝ)|=(1309480027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315058_s1_s1_7 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-794699593/2500000000 : ℝ)*x 0 + (2979980633/10000000000 : ℝ)*x 1 + (-3119076643/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (794699593/2500000000 : ℝ)^19 ≤ (4683419998789/20000000000000 : ℝ)^15 := by
    have hnat : (794699593 : ℕ)^19*20000000000000^15 ≤ 4683419998789^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      794699593 2500000000 4683419998789 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2979980633/10000000000 : ℝ)^19 ≤ (10788813779549/50000000000000 : ℝ)^15 := by
    have hnat : (2979980633 : ℕ)^19*50000000000000^15 ≤ 10788813779549^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2979980633 10000000000 10788813779549 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3119076643/5000000000 : ℝ)^19 ≤ (55005272443061/100000000000000 : ℝ)^15 := by
    have hnat : (3119076643 : ℕ)^19*100000000000000^15 ≤ 55005272443061^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3119076643 5000000000 55005272443061 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-794699593/2500000000 : ℝ), (2979980633/10000000000 : ℝ), (-3119076643/5000000000 : ℝ)] ![(4683419998789/20000000000000 : ℝ), (10788813779549/50000000000000 : ℝ), (55005272443061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-794699593/2500000000 : ℝ)|^19 ≤ (4683419998789/20000000000000 : ℝ)^15
        have hw : |(-794699593/2500000000 : ℝ)|=(794699593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2979980633/10000000000 : ℝ)|^19 ≤ (10788813779549/50000000000000 : ℝ)^15
        have hw : |(2979980633/10000000000 : ℝ)|=(2979980633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3119076643/5000000000 : ℝ)|^19 ≤ (55005272443061/100000000000000 : ℝ)^15
        have hw : |(-3119076643/5000000000 : ℝ)|=(3119076643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315058_s1_s1_8 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (797608747/2500000000 : ℝ)*x 0 + (-18530519/62500000 : ℝ)*x 1 + (-6240816111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (797608747/2500000000 : ℝ)^19 ≤ (23525735279079/100000000000000 : ℝ)^15 := by
    have hnat : (797608747 : ℕ)^19*100000000000000^15 ≤ 23525735279079^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      797608747 2500000000 23525735279079 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (18530519/62500000 : ℝ)^19 ≤ (21439249743099/100000000000000 : ℝ)^15 := by
    have hnat : (18530519 : ℕ)^19*100000000000000^15 ≤ 21439249743099^15*62500000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18530519 62500000 21439249743099 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6240816111/10000000000 : ℝ)^19 ≤ (55035014976601/100000000000000 : ℝ)^15 := by
    have hnat : (6240816111 : ℕ)^19*100000000000000^15 ≤ 55035014976601^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6240816111 10000000000 55035014976601 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(797608747/2500000000 : ℝ), (-18530519/62500000 : ℝ), (-6240816111/10000000000 : ℝ)] ![(23525735279079/100000000000000 : ℝ), (21439249743099/100000000000000 : ℝ), (55035014976601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(797608747/2500000000 : ℝ)|^19 ≤ (23525735279079/100000000000000 : ℝ)^15
        have hw : |(797608747/2500000000 : ℝ)|=(797608747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-18530519/62500000 : ℝ)|^19 ≤ (21439249743099/100000000000000 : ℝ)^15
        have hw : |(-18530519/62500000 : ℝ)|=(18530519/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6240816111/10000000000 : ℝ)|^19 ≤ (55035014976601/100000000000000 : ℝ)^15
        have hw : |(-6240816111/10000000000 : ℝ)|=(6240816111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315058_s1_s1_9 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5560211323/10000000000 : ℝ)*x 0 + (537420653/1000000000 : ℝ)*x 1 + (1213280101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5560211323/10000000000 : ℝ)^19 ≤ (47546181502447/100000000000000 : ℝ)^15 := by
    have hnat : (5560211323 : ℕ)^19*100000000000000^15 ≤ 47546181502447^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5560211323 10000000000 47546181502447 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537420653/1000000000 : ℝ)^19 ≤ (45540540376073/100000000000000 : ℝ)^15 := by
    have hnat : (537420653 : ℕ)^19*100000000000000^15 ≤ 45540540376073^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537420653 1000000000 45540540376073 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1213280101/10000000000 : ℝ)^19 ≤ (3456639054011/50000000000000 : ℝ)^15 := by
    have hnat : (1213280101 : ℕ)^19*50000000000000^15 ≤ 3456639054011^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1213280101 10000000000 3456639054011 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5560211323/10000000000 : ℝ), (537420653/1000000000 : ℝ), (1213280101/10000000000 : ℝ)] ![(47546181502447/100000000000000 : ℝ), (45540540376073/100000000000000 : ℝ), (3456639054011/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5560211323/10000000000 : ℝ)|^19 ≤ (47546181502447/100000000000000 : ℝ)^15
        have hw : |(5560211323/10000000000 : ℝ)|=(5560211323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(537420653/1000000000 : ℝ)|^19 ≤ (45540540376073/100000000000000 : ℝ)^15
        have hw : |(537420653/1000000000 : ℝ)|=(537420653/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1213280101/10000000000 : ℝ)|^19 ≤ (3456639054011/50000000000000 : ℝ)^15
        have hw : |(1213280101/10000000000 : ℝ)|=(1213280101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315058_s1_s1_13 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2154347901/5000000000 : ℝ)*x 0 + (6837882021/10000000000 : ℝ)*x 1 + (-47182759/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2154347901/5000000000 : ℝ)^19 ≤ (17211077499739/50000000000000 : ℝ)^15 := by
    have hnat : (2154347901 : ℕ)^19*50000000000000^15 ≤ 17211077499739^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2154347901 5000000000 17211077499739 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6837882021/10000000000 : ℝ)^19 ≤ (15446877634659/25000000000000 : ℝ)^15 := by
    have hnat : (6837882021 : ℕ)^19*25000000000000^15 ≤ 15446877634659^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6837882021 10000000000 15446877634659 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (47182759/625000000 : ℝ)^19 ≤ (3790334448587/100000000000000 : ℝ)^15 := by
    have hnat : (47182759 : ℕ)^19*100000000000000^15 ≤ 3790334448587^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47182759 625000000 3790334448587 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2154347901/5000000000 : ℝ), (6837882021/10000000000 : ℝ), (-47182759/625000000 : ℝ)] ![(17211077499739/50000000000000 : ℝ), (15446877634659/25000000000000 : ℝ), (3790334448587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2154347901/5000000000 : ℝ)|^19 ≤ (17211077499739/50000000000000 : ℝ)^15
        have hw : |(2154347901/5000000000 : ℝ)|=(2154347901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6837882021/10000000000 : ℝ)|^19 ≤ (15446877634659/25000000000000 : ℝ)^15
        have hw : |(6837882021/10000000000 : ℝ)|=(6837882021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-47182759/625000000 : ℝ)|^19 ≤ (3790334448587/100000000000000 : ℝ)^15
        have hw : |(-47182759/625000000 : ℝ)|=(47182759/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315058_s1_s1_14 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-789368503/2500000000 : ℝ)*x 0 + (40842033/125000000 : ℝ)*x 1 + (-6015927833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (789368503/2500000000 : ℝ)^19 ≤ (23218298697591/100000000000000 : ℝ)^15 := by
    have hnat : (789368503 : ℕ)^19*100000000000000^15 ≤ 23218298697591^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      789368503 2500000000 23218298697591 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40842033/125000000 : ℝ)^19 ≤ (24246550573481/100000000000000 : ℝ)^15 := by
    have hnat : (40842033 : ℕ)^19*100000000000000^15 ≤ 24246550573481^15*125000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40842033 125000000 24246550573481 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6015927833/10000000000 : ℝ)^19 ≤ (6566893840267/12500000000000 : ℝ)^15 := by
    have hnat : (6015927833 : ℕ)^19*12500000000000^15 ≤ 6566893840267^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6015927833 10000000000 6566893840267 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-789368503/2500000000 : ℝ), (40842033/125000000 : ℝ), (-6015927833/10000000000 : ℝ)] ![(23218298697591/100000000000000 : ℝ), (24246550573481/100000000000000 : ℝ), (6566893840267/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-789368503/2500000000 : ℝ)|^19 ≤ (23218298697591/100000000000000 : ℝ)^15
        have hw : |(-789368503/2500000000 : ℝ)|=(789368503/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40842033/125000000 : ℝ)|^19 ≤ (24246550573481/100000000000000 : ℝ)^15
        have hw : |(40842033/125000000 : ℝ)|=(40842033/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6015927833/10000000000 : ℝ)|^19 ≤ (6566893840267/12500000000000 : ℝ)^15
        have hw : |(-6015927833/10000000000 : ℝ)|=(6015927833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315058_s1_s1_15 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2878328679/10000000000 : ℝ)*x 0 + (-7459661/25000000 : ℝ)*x 1 + (-3240748919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2878328679/10000000000 : ℝ)^19 ≤ (20649576739957/100000000000000 : ℝ)^15 := by
    have hnat : (2878328679 : ℕ)^19*100000000000000^15 ≤ 20649576739957^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2878328679 10000000000 20649576739957 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7459661/25000000 : ℝ)^19 ≤ (21613254718563/100000000000000 : ℝ)^15 := by
    have hnat : (7459661 : ℕ)^19*100000000000000^15 ≤ 21613254718563^15*25000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7459661 25000000 21613254718563 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3240748919/5000000000 : ℝ)^19 ≤ (11547433705957/20000000000000 : ℝ)^15 := by
    have hnat : (3240748919 : ℕ)^19*20000000000000^15 ≤ 11547433705957^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3240748919 5000000000 11547433705957 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2878328679/10000000000 : ℝ), (-7459661/25000000 : ℝ), (-3240748919/5000000000 : ℝ)] ![(20649576739957/100000000000000 : ℝ), (21613254718563/100000000000000 : ℝ), (11547433705957/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2878328679/10000000000 : ℝ)|^19 ≤ (20649576739957/100000000000000 : ℝ)^15
        have hw : |(2878328679/10000000000 : ℝ)|=(2878328679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7459661/25000000 : ℝ)|^19 ≤ (21613254718563/100000000000000 : ℝ)^15
        have hw : |(-7459661/25000000 : ℝ)|=(7459661/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3240748919/5000000000 : ℝ)|^19 ≤ (11547433705957/20000000000000 : ℝ)^15
        have hw : |(-3240748919/5000000000 : ℝ)|=(3240748919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315058_s1_s1_16 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (228227451/400000000 : ℝ)*x 0 + (1062896493/2000000000 : ℝ)*x 1 + (540456913/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (228227451/400000000 : ℝ)^19 ≤ (49127348539121/100000000000000 : ℝ)^15 := by
    have hnat : (228227451 : ℕ)^19*100000000000000^15 ≤ 49127348539121^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228227451 400000000 49127348539121 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1062896493/2000000000 : ℝ)^19 ≤ (22450218750327/50000000000000 : ℝ)^15 := by
    have hnat : (1062896493 : ℕ)^19*50000000000000^15 ≤ 22450218750327^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062896493 2000000000 22450218750327 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540456913/5000000000 : ℝ)^19 ≤ (5972213952821/100000000000000 : ℝ)^15 := by
    have hnat : (540456913 : ℕ)^19*100000000000000^15 ≤ 5972213952821^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540456913 5000000000 5972213952821 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(228227451/400000000 : ℝ), (1062896493/2000000000 : ℝ), (540456913/5000000000 : ℝ)] ![(49127348539121/100000000000000 : ℝ), (22450218750327/50000000000000 : ℝ), (5972213952821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(228227451/400000000 : ℝ)|^19 ≤ (49127348539121/100000000000000 : ℝ)^15
        have hw : |(228227451/400000000 : ℝ)|=(228227451/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1062896493/2000000000 : ℝ)|^19 ≤ (22450218750327/50000000000000 : ℝ)^15
        have hw : |(1062896493/2000000000 : ℝ)|=(1062896493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540456913/5000000000 : ℝ)|^19 ≤ (5972213952821/100000000000000 : ℝ)^15
        have hw : |(540456913/5000000000 : ℝ)|=(540456913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315058_s1_s1_20 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (257342457/500000000 : ℝ)*x 0 + (1177284929/2000000000 : ℝ)*x 1 + (-1053227719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (257342457/500000000 : ℝ)^19 ≤ (43114083230127/100000000000000 : ℝ)^15 := by
    have hnat : (257342457 : ℕ)^19*100000000000000^15 ≤ 43114083230127^15*500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257342457 500000000 43114083230127 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1177284929/2000000000 : ℝ)^19 ≤ (2555339942409/5000000000000 : ℝ)^15 := by
    have hnat : (1177284929 : ℕ)^19*5000000000000^15 ≤ 2555339942409^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1177284929 2000000000 2555339942409 5000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053227719/10000000000 : ℝ)^19 ≤ (5779117907597/100000000000000 : ℝ)^15 := by
    have hnat : (1053227719 : ℕ)^19*100000000000000^15 ≤ 5779117907597^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053227719 10000000000 5779117907597 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(257342457/500000000 : ℝ), (1177284929/2000000000 : ℝ), (-1053227719/10000000000 : ℝ)] ![(43114083230127/100000000000000 : ℝ), (2555339942409/5000000000000 : ℝ), (5779117907597/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(257342457/500000000 : ℝ)|^19 ≤ (43114083230127/100000000000000 : ℝ)^15
        have hw : |(257342457/500000000 : ℝ)|=(257342457/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1177284929/2000000000 : ℝ)|^19 ≤ (2555339942409/5000000000000 : ℝ)^15
        have hw : |(1177284929/2000000000 : ℝ)|=(1177284929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1053227719/10000000000 : ℝ)|^19 ≤ (5779117907597/100000000000000 : ℝ)^15
        have hw : |(-1053227719/10000000000 : ℝ)|=(1053227719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315058_s1_s1_21 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-672055273/2000000000 : ℝ)*x 0 + (1650699569/5000000000 : ℝ)*x 1 + (-5813839661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672055273/2000000000 : ℝ)^19 ≤ (1570200147823/6250000000000 : ℝ)^15 := by
    have hnat : (672055273 : ℕ)^19*6250000000000^15 ≤ 1570200147823^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672055273 2000000000 1570200147823 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1650699569/5000000000 : ℝ)^19 ≤ (24566927405213/100000000000000 : ℝ)^15 := by
    have hnat : (1650699569 : ℕ)^19*100000000000000^15 ≤ 24566927405213^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1650699569 5000000000 24566927405213 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5813839661/10000000000 : ℝ)^19 ≤ (10061974043493/20000000000000 : ℝ)^15 := by
    have hnat : (5813839661 : ℕ)^19*20000000000000^15 ≤ 10061974043493^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5813839661 10000000000 10061974043493 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-672055273/2000000000 : ℝ), (1650699569/5000000000 : ℝ), (-5813839661/10000000000 : ℝ)] ![(1570200147823/6250000000000 : ℝ), (24566927405213/100000000000000 : ℝ), (10061974043493/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-672055273/2000000000 : ℝ)|^19 ≤ (1570200147823/6250000000000 : ℝ)^15
        have hw : |(-672055273/2000000000 : ℝ)|=(672055273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1650699569/5000000000 : ℝ)|^19 ≤ (24566927405213/100000000000000 : ℝ)^15
        have hw : |(1650699569/5000000000 : ℝ)|=(1650699569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5813839661/10000000000 : ℝ)|^19 ≤ (10061974043493/20000000000000 : ℝ)^15
        have hw : |(-5813839661/10000000000 : ℝ)|=(5813839661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315058_s1_s1_22 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3163907557/10000000000 : ℝ)*x 0 + (-619376673/2000000000 : ℝ)*x 1 + (-3076968803/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3163907557/10000000000 : ℝ)^19 ≤ (5819559828553/25000000000000 : ℝ)^15 := by
    have hnat : (3163907557 : ℕ)^19*25000000000000^15 ≤ 5819559828553^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3163907557 10000000000 5819559828553 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (619376673/2000000000 : ℝ)^19 ≤ (22655386504177/100000000000000 : ℝ)^15 := by
    have hnat : (619376673 : ℕ)^19*100000000000000^15 ≤ 22655386504177^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      619376673 2000000000 22655386504177 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3076968803/5000000000 : ℝ)^19 ≤ (5406637417111/10000000000000 : ℝ)^15 := by
    have hnat : (3076968803 : ℕ)^19*10000000000000^15 ≤ 5406637417111^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3076968803 5000000000 5406637417111 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3163907557/10000000000 : ℝ), (-619376673/2000000000 : ℝ), (-3076968803/5000000000 : ℝ)] ![(5819559828553/25000000000000 : ℝ), (22655386504177/100000000000000 : ℝ), (5406637417111/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3163907557/10000000000 : ℝ)|^19 ≤ (5819559828553/25000000000000 : ℝ)^15
        have hw : |(3163907557/10000000000 : ℝ)|=(3163907557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-619376673/2000000000 : ℝ)|^19 ≤ (22655386504177/100000000000000 : ℝ)^15
        have hw : |(-619376673/2000000000 : ℝ)|=(619376673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3076968803/5000000000 : ℝ)|^19 ≤ (5406637417111/10000000000000 : ℝ)^15
        have hw : |(-3076968803/5000000000 : ℝ)|=(3076968803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315058_s1_s1_23 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1170088847/2000000000 : ℝ)*x 0 + (151238601/312500000 : ℝ)*x 1 + (773693087/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1170088847/2000000000 : ℝ)^19 ≤ (792366115497/1562500000000 : ℝ)^15 := by
    have hnat : (1170088847 : ℕ)^19*1562500000000^15 ≤ 792366115497^15*2000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1170088847 2000000000 792366115497 1562500000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (151238601/312500000 : ℝ)^19 ≤ (39880690052041/100000000000000 : ℝ)^15 := by
    have hnat : (151238601 : ℕ)^19*100000000000000^15 ≤ 39880690052041^15*312500000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151238601 312500000 39880690052041 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (773693087/5000000000 : ℝ)^19 ≤ (9407878543251/100000000000000 : ℝ)^15 := by
    have hnat : (773693087 : ℕ)^19*100000000000000^15 ≤ 9407878543251^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773693087 5000000000 9407878543251 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1170088847/2000000000 : ℝ), (151238601/312500000 : ℝ), (773693087/5000000000 : ℝ)] ![(792366115497/1562500000000 : ℝ), (39880690052041/100000000000000 : ℝ), (9407878543251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1170088847/2000000000 : ℝ)|^19 ≤ (792366115497/1562500000000 : ℝ)^15
        have hw : |(1170088847/2000000000 : ℝ)|=(1170088847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(151238601/312500000 : ℝ)|^19 ≤ (39880690052041/100000000000000 : ℝ)^15
        have hw : |(151238601/312500000 : ℝ)|=(151238601/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(773693087/5000000000 : ℝ)|^19 ≤ (9407878543251/100000000000000 : ℝ)^15
        have hw : |(773693087/5000000000 : ℝ)|=(773693087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c315058_s1_s1_27 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (963019243/2500000000 : ℝ)*x 0 + (718015737/1000000000 : ℝ)*x 1 + (-849348653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (963019243/2500000000 : ℝ)^19 ≤ (5973702735219/20000000000000 : ℝ)^15 := by
    have hnat : (963019243 : ℕ)^19*20000000000000^15 ≤ 5973702735219^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      963019243 2500000000 5973702735219 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (718015737/1000000000 : ℝ)^19 ≤ (32865458143703/50000000000000 : ℝ)^15 := by
    have hnat : (718015737 : ℕ)^19*50000000000000^15 ≤ 32865458143703^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      718015737 1000000000 32865458143703 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (849348653/10000000000 : ℝ)^19 ≤ (880114005293/20000000000000 : ℝ)^15 := by
    have hnat : (849348653 : ℕ)^19*20000000000000^15 ≤ 880114005293^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849348653 10000000000 880114005293 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(963019243/2500000000 : ℝ), (718015737/1000000000 : ℝ), (-849348653/10000000000 : ℝ)] ![(5973702735219/20000000000000 : ℝ), (32865458143703/50000000000000 : ℝ), (880114005293/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(963019243/2500000000 : ℝ)|^19 ≤ (5973702735219/20000000000000 : ℝ)^15
        have hw : |(963019243/2500000000 : ℝ)|=(963019243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(718015737/1000000000 : ℝ)|^19 ≤ (32865458143703/50000000000000 : ℝ)^15
        have hw : |(718015737/1000000000 : ℝ)|=(718015737/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-849348653/10000000000 : ℝ)|^19 ≤ (880114005293/20000000000000 : ℝ)^15
        have hw : |(-849348653/10000000000 : ℝ)|=(849348653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c315058_s1 (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((20281/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20281/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75473/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75473/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-65217/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-65217/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((17087/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17087/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(941/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(941/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-4059/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-4059/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15821/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15821/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15821/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15821/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15821/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base60 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 1+(1 : ℝ)*X 1 0+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (20281/25000 : ℝ) ^ (75/16 : ℝ) ≤ (1500367331311232819/4000000000000000000 : ℝ) := by
    have hpowers : (20281/25000 : ℝ)^75 ≤ (1500367331311232819/4000000000000000000 : ℝ)^16 := by
      have hnat : (20281 : ℕ)^75*4000000000000000000^16 ≤ 1500367331311232819^16*25000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20281 25000 1500367331311232819 4000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20281/25000 : ℝ)) (X := (1500367331311232819/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0a : (5500367331311232819/4000000000000000000 : ℝ) ≤ (2140625816841353/2000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (5500367331311232819/4000000000000000000 : ℝ)^16 ≤ (2140625816841353/2000000000000000 : ℝ)^75 := by
      have hnat : (5500367331311232819 : ℕ)^16*2000000000000000^75 ≤ 2140625816841353^75*4000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5500367331311232819 4000000000000000000 2140625816841353 2000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2140625816841353/2000000000000000 : ℝ)) (X := (5500367331311232819/4000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner0b : (3500367331311232819/2000000000000000000 : ℝ) ≤ (1408535681911083/1250000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (3500367331311232819/2000000000000000000 : ℝ)^16 ≤ (1408535681911083/1250000000000000 : ℝ)^75 := by
      have hnat : (3500367331311232819 : ℕ)^16*1250000000000000^75 ≤ 1408535681911083^75*2000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3500367331311232819 2000000000000000000 1408535681911083 1250000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1408535681911083/1250000000000000 : ℝ)) (X := (3500367331311232819/2000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(140625816841353/1622480000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(565156371081899/8112400000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (20281/25000 : ℝ)) (alpha := (140625816841353/1622480000000000 : ℝ)) (beta := (565156371081899/8112400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (20281/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(140625816841353/1622480000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(565156371081899/8112400000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (75473/100000 : ℝ) ^ (75/16 : ℝ) ≤ (26739186297478875949/100000000000000000000 : ℝ) := by
    have hpowers : (75473/100000 : ℝ)^75 ≤ (26739186297478875949/100000000000000000000 : ℝ)^16 := by
      have hnat : (75473 : ℕ)^75*100000000000000000000^16 ≤ 26739186297478875949^16*100000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        75473 100000 26739186297478875949 100000000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (75473/100000 : ℝ)) (X := (26739186297478875949/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1a : (126739186297478875949/100000000000000000000 : ℝ) ≤ (525925626253207/500000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (126739186297478875949/100000000000000000000 : ℝ)^16 ≤ (525925626253207/500000000000000 : ℝ)^75 := by
      have hnat : (126739186297478875949 : ℕ)^16*500000000000000^75 ≤ 525925626253207^75*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        126739186297478875949 100000000000000000000 525925626253207 500000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (525925626253207/500000000000000 : ℝ)) (X := (126739186297478875949/100000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner1b : (76739186297478875949/50000000000000000000 : ℝ) ≤ (42800624019199/39062500000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (76739186297478875949/50000000000000000000 : ℝ)^16 ≤ (42800624019199/39062500000000 : ℝ)^75 := by
      have hnat : (76739186297478875949 : ℕ)^16*39062500000000^75 ≤ 42800624019199^75*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        76739186297478875949 50000000000000000000 42800624019199 39062500000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (42800624019199/39062500000000 : ℝ)) (X := (76739186297478875949/50000000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(25925626253207/377365000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(109611805962701/1886825000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (75473/100000 : ℝ)) (alpha := (25925626253207/377365000000000 : ℝ)) (beta := (109611805962701/1886825000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (75473/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(25925626253207/377365000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(109611805962701/1886825000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (65217/100000 : ℝ) ^ (75/16 : ℝ) ≤ (842745317719814213/6250000000000000000 : ℝ) := by
    have hpowers : (65217/100000 : ℝ)^75 ≤ (842745317719814213/6250000000000000000 : ℝ)^16 := by
      have hnat : (65217 : ℕ)^75*6250000000000000000^16 ≤ 842745317719814213^16*100000^75 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        65217 100000 842745317719814213 6250000000000000000 75 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (65217/100000 : ℝ)) (X := (842745317719814213/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2a : (7092745317719814213/6250000000000000000 : ℝ) ≤ (5136760673299867/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (7092745317719814213/6250000000000000000 : ℝ)^16 ≤ (5136760673299867/5000000000000000 : ℝ)^75 := by
      have hnat : (7092745317719814213 : ℕ)^16*5000000000000000^75 ≤ 5136760673299867^75*6250000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7092745317719814213 6250000000000000000 5136760673299867 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5136760673299867/5000000000000000 : ℝ)) (X := (7092745317719814213/6250000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have s1_corner2b : (3967745317719814213/3125000000000000000 : ℝ) ≤ (5261279103349271/5000000000000000 : ℝ) ^ (75/16 : ℝ) := by
    have hpowers : (3967745317719814213/3125000000000000000 : ℝ)^16 ≤ (5261279103349271/5000000000000000 : ℝ)^75 := by
      have hnat : (3967745317719814213 : ℕ)^16*5000000000000000^75 ≤ 5261279103349271^75*3125000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3967745317719814213 3125000000000000000 5261279103349271 5000000000000000 16 75 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5261279103349271/5000000000000000 : ℝ)) (X := (3967745317719814213/3125000000000000000 : ℝ)) (by norm_num) 75 16 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(136760673299867/3260850000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(31129607512351/815212500000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (75/16 : ℝ)) (rho := (65217/100000 : ℝ)) (alpha := (136760673299867/3260850000000000 : ℝ)) (beta := (31129607512351/815212500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (65217/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(136760673299867/3260850000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(31129607512351/815212500000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-212175587/625000000 : ℝ)*X 0 0+(1665797771/5000000000 : ℝ)*X 0 1+(-1439473073/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315058_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((62475033/200000000 : ℝ)*X 1 0+(-23915421/78125000 : ℝ)*X 1 1+(-1554277663/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315058_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((684390881/1250000000 : ℝ)*X 2 0+(2640939681/5000000000 : ℝ)*X 2 1+(183844807/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315058_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4635464587/10000000000 : ℝ)*X 0 0+(775493363/1250000000 : ℝ)*X 0 1+(-1309480027/10000000000 : ℝ)*X 0 2+(4635464587/10000000000 : ℝ)*X 1 0+(775493363/1250000000 : ℝ)*X 1 1+(-1309480027/10000000000 : ℝ)*X 1 2+(4635464587/10000000000 : ℝ)*X 2 0+(775493363/1250000000 : ℝ)*X 2 1+(-1309480027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315058_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-794699593/2500000000 : ℝ)*X 0 0+(2979980633/10000000000 : ℝ)*X 0 1+(-3119076643/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315058_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((797608747/2500000000 : ℝ)*X 1 0+(-18530519/62500000 : ℝ)*X 1 1+(-6240816111/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315058_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((5560211323/10000000000 : ℝ)*X 2 0+(537420653/1000000000 : ℝ)*X 2 1+(1213280101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315058_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((2154347901/5000000000 : ℝ)*X 0 0+(6837882021/10000000000 : ℝ)*X 0 1+(-47182759/625000000 : ℝ)*X 0 2+(2154347901/5000000000 : ℝ)*X 1 0+(6837882021/10000000000 : ℝ)*X 1 1+(-47182759/625000000 : ℝ)*X 1 2+(2154347901/5000000000 : ℝ)*X 2 0+(6837882021/10000000000 : ℝ)*X 2 1+(-47182759/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315058_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-789368503/2500000000 : ℝ)*X 0 0+(40842033/125000000 : ℝ)*X 0 1+(-6015927833/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315058_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2878328679/10000000000 : ℝ)*X 1 0+(-7459661/25000000 : ℝ)*X 1 1+(-3240748919/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315058_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((228227451/400000000 : ℝ)*X 2 0+(1062896493/2000000000 : ℝ)*X 2 1+(540456913/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315058_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((257342457/500000000 : ℝ)*X 0 0+(1177284929/2000000000 : ℝ)*X 0 1+(-1053227719/10000000000 : ℝ)*X 0 2+(257342457/500000000 : ℝ)*X 1 0+(1177284929/2000000000 : ℝ)*X 1 1+(-1053227719/10000000000 : ℝ)*X 1 2+(257342457/500000000 : ℝ)*X 2 0+(1177284929/2000000000 : ℝ)*X 2 1+(-1053227719/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315058_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-672055273/2000000000 : ℝ)*X 0 0+(1650699569/5000000000 : ℝ)*X 0 1+(-5813839661/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c315058_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((3163907557/10000000000 : ℝ)*X 1 0+(-619376673/2000000000 : ℝ)*X 1 1+(-3076968803/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c315058_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((1170088847/2000000000 : ℝ)*X 2 0+(151238601/312500000 : ℝ)*X 2 1+(773693087/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c315058_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((963019243/2500000000 : ℝ)*X 0 0+(718015737/1000000000 : ℝ)*X 0 1+(-849348653/10000000000 : ℝ)*X 0 2+(963019243/2500000000 : ℝ)*X 1 0+(718015737/1000000000 : ℝ)*X 1 1+(-849348653/10000000000 : ℝ)*X 1 2+(963019243/2500000000 : ℝ)*X 2 0+(718015737/1000000000 : ℝ)*X 2 1+(-849348653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c315058_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((17087/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17087/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (281405519921734981194132937/41017688675000000000000000000000 : ℝ) := by norm_num
    linear_combination (152976935461/200000000000 : ℝ)*(base5) + (184670845087/1000000000000 : ℝ)*(base49) + (1971151001251/500000000000 : ℝ)*(base60) + (15450337461869/1000000000000 : ℝ)*(major_s1_0) + (15450337461869/1000000000000 : ℝ)*(major_s1_1) + (15450337461869/1000000000000 : ℝ)*(major_s1_2) + (326819827/1000000000000 : ℝ)*(sp_s1_1) + (520163/4000000000 : ℝ)*(sp_s1_2) + (2673339/125000000000 : ℝ)*(sp_s1_6) + (22054671307497/1000000000000 : ℝ)*(sp_s1_7) + (11027172090723/500000000000 : ℝ)*(sp_s1_8) + (5704856486013/250000000000 : ℝ)*(sp_s1_9) + (2020273816339/250000000000 : ℝ)*(sp_s1_13) + (12249/40000000000 : ℝ)*(sp_s1_15) + (8846001329373/1000000000000 : ℝ)*(f.failure) + (22054671307497/1000000000000 : ℝ)*(f.sum) + (20796875022708925229/246106132050000000000000000000000 : ℝ)*base62 + (1112156824000549/3260850000000000000000000000 : ℝ)*base64 + (22293563537339/471706250000000000000000000 : ℝ)*base66 + (255954500994611/407606250000000000000000000 : ℝ)*base68 + (104296723091138520553/529066390800000000000000000000000 : ℝ)*base71 + (7044149325456751/8112400000000000000000000000 : ℝ)*base73 + (29183984092143/75473000000000000000000000 : ℝ)*base74 + (4926555405639/12979840000000000000000000 : ℝ)*base76 + (212994011728074762193/612267165200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base83 + (58807/100000000000000000 : ℝ)*base87 + (58807/100000000000000000 : ℝ)*base89 + (58807/100000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(941/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(941/3125 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (147019124670630862521708075449/7829456414284000000000000000000000 : ℝ) := by norm_num
    linear_combination (7514253694537/1000000000000 : ℝ)*(base5) + (2096171/200000000000 : ℝ)*(base39) + (1119301462761/1000000000000 : ℝ)*(base49) + (299582832037/40000000000 : ℝ)*(base60) + (2868859140289/200000000000 : ℝ)*(major_s1_0) + (2868859140289/200000000000 : ℝ)*(major_s1_1) + (2868859140289/200000000000 : ℝ)*(major_s1_2) + (238641451/1000000000000 : ℝ)*(sp_s1_7) + (5118859532587/250000000000 : ℝ)*(sp_s1_14) + (20475841625459/1000000000000 : ℝ)*(sp_s1_15) + (44784030129/1600000000 : ℝ)*(sp_s1_16) + (349244911829/500000000000 : ℝ)*(sp_s1_20) + (8242683/50000000000 : ℝ)*(sp_s1_21) + (76489371/1000000000000 : ℝ)*(sp_s1_23) + (2053185879549/250000000000 : ℝ)*(f.failure) + (20475841625459/1000000000000 : ℝ)*(f.sum) + (15752107748639479259/49221226410000000000000000000000 : ℝ)*base63 + (254054585771/5217360000000000000000000 : ℝ)*base65 + (72279947091043/377365000000000000000000000 : ℝ)*base66 + (799621108999/16304250000000000000000000 : ℝ)*base69 + (2044629162794007469/6224310480000000000000000000000 : ℝ)*base71 + (23398788774981/95440000000000000000000000 : ℝ)*base72 + (332388301291/75473000000000000000000000 : ℝ)*base74 + (5056266409797/95440000000000000000000000 : ℝ)*base77 + (7118589388469921333/7203143120000000000000000000000 : ℝ)*base78 + (23791/25000000000000000 : ℝ)*base87 + (23791/25000000000000000 : ℝ)*base89 + (23791/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-4059/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-4059/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (207146393260656593417479263/22044432950000000000000000000000 : ℝ) := by norm_num
    linear_combination (15043721987/25000000000 : ℝ)*(base5) + (554875732223/1000000000000 : ℝ)*(base49) + (374056899213/200000000000 : ℝ)*(base60) + (9229424118487/1000000000000 : ℝ)*(major_s1_0) + (9229424118487/1000000000000 : ℝ)*(major_s1_1) + (9229424118487/1000000000000 : ℝ)*(major_s1_2) + (548816877/500000000000 : ℝ)*(sp_s1_0) + (17445607/500000000000 : ℝ)*(sp_s1_2) + (18057389/100000000000 : ℝ)*(sp_s1_9) + (146589353/1000000000000 : ℝ)*(sp_s1_14) + (1646668437163/125000000000 : ℝ)*(sp_s1_21) + (1317459172041/100000000000 : ℝ)*(sp_s1_22) + (6888062567393/500000000000 : ℝ)*(sp_s1_23) + (2341252252411/500000000000 : ℝ)*(sp_s1_27) + (5284253384301/1000000000000 : ℝ)*(f.failure) + (1317459172041/100000000000 : ℝ)*(f.sum) + (72994493958185379113/246106132050000000000000000000000 : ℝ)*base63 + (274574904484013/815212500000000000000000000 : ℝ)*base64 + (1237656372284129/3773650000000000000000000000 : ℝ)*base67 + (428422032979681/3260850000000000000000000000 : ℝ)*base69 + (91641853063939756261/529066390800000000000000000000000 : ℝ)*base70 + (1012589720372947/8112400000000000000000000000 : ℝ)*base72 + (8039080432061/75473000000000000000000000 : ℝ)*base74 + (418835034050769/1622480000000000000000000000 : ℝ)*base76 + (60558595596692291939/612267165200000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (71641/100000000000000000 : ℝ)*base86 + (71641/100000000000000000 : ℝ)*base88 + (71641/100000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (75/16 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (174659/100000 : ℝ) (34911/20000 : ℝ) (15821/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((20281/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(20281/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(75473/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(75473/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-65217/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-65217/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((17087/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(17087/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(941/3125 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(941/3125 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-4059/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-4059/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c315058_s1 p hpa hpb X hX hprev0

#print axioms solution
