-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c320063_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:37:18.461576+00:00
-- url     : https://prove2.me/submissions/71b16386-9ae3-447a-be90-fcbf2cf1d17c

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
theorem collision_support_c320063_s2_s2_0 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1339644187/10000000000 : ℝ)*x 0 + (668249249/1250000000 : ℝ)*x 1 + (5363475179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1339644187/10000000000 : ℝ)^81 ≤ (408380096177/5000000000000 : ℝ)^65 := by
    have hnat : (1339644187 : ℕ)^81*5000000000000^65 ≤ 408380096177^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339644187 10000000000 408380096177 5000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (668249249/1250000000 : ℝ)^81 ≤ (45822800431101/100000000000000 : ℝ)^65 := by
    have hnat : (668249249 : ℕ)^81*100000000000000^65 ≤ 45822800431101^65*1250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668249249 1250000000 45822800431101 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5363475179/10000000000 : ℝ)^81 ≤ (23004798812509/50000000000000 : ℝ)^65 := by
    have hnat : (5363475179 : ℕ)^81*50000000000000^65 ≤ 23004798812509^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5363475179 10000000000 23004798812509 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1339644187/10000000000 : ℝ), (668249249/1250000000 : ℝ), (5363475179/10000000000 : ℝ)] ![(408380096177/5000000000000 : ℝ), (45822800431101/100000000000000 : ℝ), (23004798812509/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1339644187/10000000000 : ℝ)|^81 ≤ (408380096177/5000000000000 : ℝ)^65
        have hw : |(-1339644187/10000000000 : ℝ)|=(1339644187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(668249249/1250000000 : ℝ)|^81 ≤ (45822800431101/100000000000000 : ℝ)^65
        have hw : |(668249249/1250000000 : ℝ)|=(668249249/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5363475179/10000000000 : ℝ)|^81 ≤ (23004798812509/50000000000000 : ℝ)^65
        have hw : |(5363475179/10000000000 : ℝ)|=(5363475179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s2_s2_1 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1336627901/2500000000 : ℝ)*x 0 + (-1343910967/10000000000 : ℝ)*x 1 + (334995249/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336627901/2500000000 : ℝ)^81 ≤ (1145708231877/2500000000000 : ℝ)^65 := by
    have hnat : (1336627901 : ℕ)^81*2500000000000^65 ≤ 1145708231877^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336627901 2500000000 1145708231877 2500000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1343910967/10000000000 : ℝ)^81 ≤ (4100015966911/50000000000000 : ℝ)^65 := by
    have hnat : (1343910967 : ℕ)^81*50000000000000^65 ≤ 4100015966911^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343910967 10000000000 4100015966911 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (334995249/625000000 : ℝ)^81 ≤ (11492909695979/25000000000000 : ℝ)^65 := by
    have hnat : (334995249 : ℕ)^81*25000000000000^65 ≤ 11492909695979^65*625000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334995249 625000000 11492909695979 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336627901/2500000000 : ℝ), (-1343910967/10000000000 : ℝ), (334995249/625000000 : ℝ)] ![(1145708231877/2500000000000 : ℝ), (4100015966911/50000000000000 : ℝ), (11492909695979/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336627901/2500000000 : ℝ)|^81 ≤ (1145708231877/2500000000000 : ℝ)^65
        have hw : |(1336627901/2500000000 : ℝ)|=(1336627901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1343910967/10000000000 : ℝ)|^81 ≤ (4100015966911/50000000000000 : ℝ)^65
        have hw : |(-1343910967/10000000000 : ℝ)|=(1343910967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(334995249/625000000 : ℝ)|^81 ≤ (11492909695979/25000000000000 : ℝ)^65
        have hw : |(334995249/625000000 : ℝ)|=(334995249/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s2_s2_2 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5360194039/10000000000 : ℝ)*x 0 + (1071466277/2000000000 : ℝ)*x 1 + (-1328305433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5360194039/10000000000 : ℝ)^81 ≤ (9194905038667/20000000000000 : ℝ)^65 := by
    have hnat : (5360194039 : ℕ)^81*20000000000000^65 ≤ 9194905038667^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5360194039 10000000000 9194905038667 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1071466277/2000000000 : ℝ)^81 ≤ (45943930316313/100000000000000 : ℝ)^65 := by
    have hnat : (1071466277 : ℕ)^81*100000000000000^65 ≤ 45943930316313^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071466277 2000000000 45943930316313 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1328305433/10000000000 : ℝ)^81 ≤ (8081544472831/100000000000000 : ℝ)^65 := by
    have hnat : (1328305433 : ℕ)^81*100000000000000^65 ≤ 8081544472831^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328305433 10000000000 8081544472831 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5360194039/10000000000 : ℝ), (1071466277/2000000000 : ℝ), (-1328305433/10000000000 : ℝ)] ![(9194905038667/20000000000000 : ℝ), (45943930316313/100000000000000 : ℝ), (8081544472831/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5360194039/10000000000 : ℝ)|^81 ≤ (9194905038667/20000000000000 : ℝ)^65
        have hw : |(5360194039/10000000000 : ℝ)|=(5360194039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1071466277/2000000000 : ℝ)|^81 ≤ (45943930316313/100000000000000 : ℝ)^65
        have hw : |(1071466277/2000000000 : ℝ)|=(1071466277/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1328305433/10000000000 : ℝ)|^81 ≤ (8081544472831/100000000000000 : ℝ)^65
        have hw : |(-1328305433/10000000000 : ℝ)|=(1328305433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s2_s2_6 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4146952889/10000000000 : ℝ)*x 0 + (4144496449/10000000000 : ℝ)*x 1 + (4132110101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4146952889/10000000000 : ℝ)^81 ≤ (16695585502807/50000000000000 : ℝ)^65 := by
    have hnat : (4146952889 : ℕ)^81*50000000000000^65 ≤ 16695585502807^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4146952889 10000000000 16695585502807 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4144496449/10000000000 : ℝ)^81 ≤ (16683262438707/50000000000000 : ℝ)^65 := by
    have hnat : (4144496449 : ℕ)^81*50000000000000^65 ≤ 16683262438707^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4144496449 10000000000 16683262438707 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4132110101/10000000000 : ℝ)^81 ≤ (33242304098333/100000000000000 : ℝ)^65 := by
    have hnat : (4132110101 : ℕ)^81*100000000000000^65 ≤ 33242304098333^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4132110101 10000000000 33242304098333 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4146952889/10000000000 : ℝ), (4144496449/10000000000 : ℝ), (4132110101/10000000000 : ℝ)] ![(16695585502807/50000000000000 : ℝ), (16683262438707/50000000000000 : ℝ), (33242304098333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4146952889/10000000000 : ℝ)|^81 ≤ (16695585502807/50000000000000 : ℝ)^65
        have hw : |(4146952889/10000000000 : ℝ)|=(4146952889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4144496449/10000000000 : ℝ)|^81 ≤ (16683262438707/50000000000000 : ℝ)^65
        have hw : |(4144496449/10000000000 : ℝ)|=(4144496449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4132110101/10000000000 : ℝ)|^81 ≤ (33242304098333/100000000000000 : ℝ)^65
        have hw : |(4132110101/10000000000 : ℝ)|=(4132110101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s2_s2_7 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-313971919/2500000000 : ℝ)*x 0 + (36620239/78125000 : ℝ)*x 1 + (6059532669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (313971919/2500000000 : ℝ)^81 ≤ (1884057187423/25000000000000 : ℝ)^65 := by
    have hnat : (313971919 : ℕ)^81*25000000000000^65 ≤ 1884057187423^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      313971919 2500000000 1884057187423 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (36620239/78125000 : ℝ)^81 ≤ (38898206672843/100000000000000 : ℝ)^65 := by
    have hnat : (36620239 : ℕ)^81*100000000000000^65 ≤ 38898206672843^65*78125000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36620239 78125000 38898206672843 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6059532669/10000000000 : ℝ)^81 ≤ (26782782283891/50000000000000 : ℝ)^65 := by
    have hnat : (6059532669 : ℕ)^81*50000000000000^65 ≤ 26782782283891^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6059532669 10000000000 26782782283891 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-313971919/2500000000 : ℝ), (36620239/78125000 : ℝ), (6059532669/10000000000 : ℝ)] ![(1884057187423/25000000000000 : ℝ), (38898206672843/100000000000000 : ℝ), (26782782283891/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-313971919/2500000000 : ℝ)|^81 ≤ (1884057187423/25000000000000 : ℝ)^65
        have hw : |(-313971919/2500000000 : ℝ)|=(313971919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(36620239/78125000 : ℝ)|^81 ≤ (38898206672843/100000000000000 : ℝ)^65
        have hw : |(36620239/78125000 : ℝ)|=(36620239/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6059532669/10000000000 : ℝ)|^81 ≤ (26782782283891/50000000000000 : ℝ)^65
        have hw : |(6059532669/10000000000 : ℝ)|=(6059532669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s2_s2_8 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2532457261/5000000000 : ℝ)*x 0 + (-87422903/1250000000 : ℝ)*x 1 + (6055959433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2532457261/5000000000 : ℝ)^81 ≤ (10710048073723/25000000000000 : ℝ)^65 := by
    have hnat : (2532457261 : ℕ)^81*25000000000000^65 ≤ 10710048073723^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2532457261 5000000000 10710048073723 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (87422903/1250000000 : ℝ)^81 ≤ (72672050131/2000000000000 : ℝ)^65 := by
    have hnat : (87422903 : ℕ)^81*2000000000000^65 ≤ 72672050131^65*1250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87422903 1250000000 72672050131 2000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6055959433/10000000000 : ℝ)^81 ≤ (167269391171/312500000000 : ℝ)^65 := by
    have hnat : (6055959433 : ℕ)^81*312500000000^65 ≤ 167269391171^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6055959433 10000000000 167269391171 312500000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2532457261/5000000000 : ℝ), (-87422903/1250000000 : ℝ), (6055959433/10000000000 : ℝ)] ![(10710048073723/25000000000000 : ℝ), (72672050131/2000000000000 : ℝ), (167269391171/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2532457261/5000000000 : ℝ)|^81 ≤ (10710048073723/25000000000000 : ℝ)^65
        have hw : |(2532457261/5000000000 : ℝ)|=(2532457261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-87422903/1250000000 : ℝ)|^81 ≤ (72672050131/2000000000000 : ℝ)^65
        have hw : |(-87422903/1250000000 : ℝ)|=(87422903/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6055959433/10000000000 : ℝ)|^81 ≤ (167269391171/312500000000 : ℝ)^65
        have hw : |(6055959433/10000000000 : ℝ)|=(6055959433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s2_s2_9 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2432990493/5000000000 : ℝ)*x 0 + (1564576941/2500000000 : ℝ)*x 1 + (-675926457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2432990493/5000000000 : ℝ)^81 ≤ (2547101300307/6250000000000 : ℝ)^65 := by
    have hnat : (2432990493 : ℕ)^81*6250000000000^65 ≤ 2547101300307^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2432990493 5000000000 2547101300307 6250000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1564576941/2500000000 : ℝ)^81 ≤ (55764010941213/100000000000000 : ℝ)^65 := by
    have hnat : (1564576941 : ℕ)^81*100000000000000^65 ≤ 55764010941213^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1564576941 2500000000 55764010941213 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675926457/10000000000 : ℝ)^81 ≤ (1741184123077/50000000000000 : ℝ)^65 := by
    have hnat : (675926457 : ℕ)^81*50000000000000^65 ≤ 1741184123077^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675926457 10000000000 1741184123077 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2432990493/5000000000 : ℝ), (1564576941/2500000000 : ℝ), (-675926457/10000000000 : ℝ)] ![(2547101300307/6250000000000 : ℝ), (55764010941213/100000000000000 : ℝ), (1741184123077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2432990493/5000000000 : ℝ)|^81 ≤ (2547101300307/6250000000000 : ℝ)^65
        have hw : |(2432990493/5000000000 : ℝ)|=(2432990493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1564576941/2500000000 : ℝ)|^81 ≤ (55764010941213/100000000000000 : ℝ)^65
        have hw : |(1564576941/2500000000 : ℝ)|=(1564576941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-675926457/10000000000 : ℝ)|^81 ≤ (1741184123077/50000000000000 : ℝ)^65
        have hw : |(-675926457/10000000000 : ℝ)|=(675926457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s2_s2_13 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4478051281/10000000000 : ℝ)*x 0 + (546878849/1000000000 : ℝ)*x 1 + (1155656549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4478051281/10000000000 : ℝ)^81 ≤ (36745426576789/100000000000000 : ℝ)^65 := by
    have hnat : (4478051281 : ℕ)^81*100000000000000^65 ≤ 36745426576789^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4478051281 10000000000 36745426576789 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (546878849/1000000000 : ℝ)^81 ≤ (23569047091269/50000000000000 : ℝ)^65 := by
    have hnat : (546878849 : ℕ)^81*50000000000000^65 ≤ 23569047091269^65*1000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546878849 1000000000 23569047091269 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1155656549/5000000000 : ℝ)^81 ≤ (8058239609067/50000000000000 : ℝ)^65 := by
    have hnat : (1155656549 : ℕ)^81*50000000000000^65 ≤ 8058239609067^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1155656549 5000000000 8058239609067 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4478051281/10000000000 : ℝ), (546878849/1000000000 : ℝ), (1155656549/5000000000 : ℝ)] ![(36745426576789/100000000000000 : ℝ), (23569047091269/50000000000000 : ℝ), (8058239609067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4478051281/10000000000 : ℝ)|^81 ≤ (36745426576789/100000000000000 : ℝ)^65
        have hw : |(4478051281/10000000000 : ℝ)|=(4478051281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(546878849/1000000000 : ℝ)|^81 ≤ (23569047091269/50000000000000 : ℝ)^65
        have hw : |(546878849/1000000000 : ℝ)|=(546878849/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1155656549/5000000000 : ℝ)|^81 ≤ (8058239609067/50000000000000 : ℝ)^65
        have hw : |(1155656549/5000000000 : ℝ)|=(1155656549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s2_s2_14 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-139804007/2000000000 : ℝ)*x 0 + (5072990411/10000000000 : ℝ)*x 1 + (6048441903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (139804007/2000000000 : ℝ)^81 ≤ (3631251256637/100000000000000 : ℝ)^65 := by
    have hnat : (139804007 : ℕ)^81*100000000000000^65 ≤ 3631251256637^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139804007 2000000000 3631251256637 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5072990411/10000000000 : ℝ)^81 ≤ (42925330889983/100000000000000 : ℝ)^65 := by
    have hnat : (5072990411 : ℕ)^81*100000000000000^65 ≤ 42925330889983^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5072990411 10000000000 42925330889983 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6048441903/10000000000 : ℝ)^81 ≤ (53443417830343/100000000000000 : ℝ)^65 := by
    have hnat : (6048441903 : ℕ)^81*100000000000000^65 ≤ 53443417830343^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6048441903 10000000000 53443417830343 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-139804007/2000000000 : ℝ), (5072990411/10000000000 : ℝ), (6048441903/10000000000 : ℝ)] ![(3631251256637/100000000000000 : ℝ), (42925330889983/100000000000000 : ℝ), (53443417830343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-139804007/2000000000 : ℝ)|^81 ≤ (3631251256637/100000000000000 : ℝ)^65
        have hw : |(-139804007/2000000000 : ℝ)|=(139804007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5072990411/10000000000 : ℝ)|^81 ≤ (42925330889983/100000000000000 : ℝ)^65
        have hw : |(5072990411/10000000000 : ℝ)|=(5072990411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6048441903/10000000000 : ℝ)|^81 ≤ (53443417830343/100000000000000 : ℝ)^65
        have hw : |(6048441903/10000000000 : ℝ)|=(6048441903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s2_s2_15 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1176402847/2500000000 : ℝ)*x 0 + (-1252273237/10000000000 : ℝ)*x 1 + (604486797/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1176402847/2500000000 : ℝ)^81 ≤ (9771680315739/25000000000000 : ℝ)^65 := by
    have hnat : (1176402847 : ℕ)^81*25000000000000^65 ≤ 9771680315739^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1176402847 2500000000 9771680315739 25000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1252273237/10000000000 : ℝ)^81 ≤ (7509210210573/100000000000000 : ℝ)^65 := by
    have hnat : (1252273237 : ℕ)^81*100000000000000^65 ≤ 7509210210573^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252273237 10000000000 7509210210573 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (604486797/1000000000 : ℝ)^81 ≤ (53404068514097/100000000000000 : ℝ)^65 := by
    have hnat : (604486797 : ℕ)^81*100000000000000^65 ≤ 53404068514097^65*1000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604486797 1000000000 53404068514097 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1176402847/2500000000 : ℝ), (-1252273237/10000000000 : ℝ), (604486797/1000000000 : ℝ)] ![(9771680315739/25000000000000 : ℝ), (7509210210573/100000000000000 : ℝ), (53404068514097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1176402847/2500000000 : ℝ)|^81 ≤ (9771680315739/25000000000000 : ℝ)^65
        have hw : |(1176402847/2500000000 : ℝ)|=(1176402847/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1252273237/10000000000 : ℝ)|^81 ≤ (7509210210573/100000000000000 : ℝ)^65
        have hw : |(-1252273237/10000000000 : ℝ)|=(1252273237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(604486797/1000000000 : ℝ)|^81 ≤ (53404068514097/100000000000000 : ℝ)^65
        have hw : |(604486797/1000000000 : ℝ)|=(604486797/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s2_s2_16 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1511137529/2500000000 : ℝ)*x 0 + (2542201689/5000000000 : ℝ)*x 1 + (-343509213/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1511137529/2500000000 : ℝ)^81 ≤ (10680113838177/20000000000000 : ℝ)^65 := by
    have hnat : (1511137529 : ℕ)^81*20000000000000^65 ≤ 10680113838177^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1511137529 2500000000 10680113838177 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2542201689/5000000000 : ℝ)^81 ≤ (1345178341129/3125000000000 : ℝ)^65 := by
    have hnat : (2542201689 : ℕ)^81*3125000000000^65 ≤ 1345178341129^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2542201689 5000000000 1345178341129 3125000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (343509213/5000000000 : ℝ)^81 ≤ (3553723873963/100000000000000 : ℝ)^65 := by
    have hnat : (343509213 : ℕ)^81*100000000000000^65 ≤ 3553723873963^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343509213 5000000000 3553723873963 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1511137529/2500000000 : ℝ), (2542201689/5000000000 : ℝ), (-343509213/5000000000 : ℝ)] ![(10680113838177/20000000000000 : ℝ), (1345178341129/3125000000000 : ℝ), (3553723873963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1511137529/2500000000 : ℝ)|^81 ≤ (10680113838177/20000000000000 : ℝ)^65
        have hw : |(1511137529/2500000000 : ℝ)|=(1511137529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2542201689/5000000000 : ℝ)|^81 ≤ (1345178341129/3125000000000 : ℝ)^65
        have hw : |(2542201689/5000000000 : ℝ)|=(2542201689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-343509213/5000000000 : ℝ)|^81 ≤ (3553723873963/100000000000000 : ℝ)^65
        have hw : |(-343509213/5000000000 : ℝ)|=(343509213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s2_s2_20 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6008371131/10000000000 : ℝ)*x 0 + (483491193/1250000000 : ℝ)*x 1 + (585466667/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6008371131/10000000000 : ℝ)^81 ≤ (53002563378229/100000000000000 : ℝ)^65 := by
    have hnat : (6008371131 : ℕ)^81*100000000000000^65 ≤ 53002563378229^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6008371131 10000000000 53002563378229 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (483491193/1250000000 : ℝ)^81 ≤ (30615038803239/100000000000000 : ℝ)^65 := by
    have hnat : (483491193 : ℕ)^81*100000000000000^65 ≤ 30615038803239^65*1250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483491193 1250000000 30615038803239 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (585466667/2500000000 : ℝ)^81 ≤ (16382397806791/100000000000000 : ℝ)^65 := by
    have hnat : (585466667 : ℕ)^81*100000000000000^65 ≤ 16382397806791^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      585466667 2500000000 16382397806791 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6008371131/10000000000 : ℝ), (483491193/1250000000 : ℝ), (585466667/2500000000 : ℝ)] ![(53002563378229/100000000000000 : ℝ), (30615038803239/100000000000000 : ℝ), (16382397806791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6008371131/10000000000 : ℝ)|^81 ≤ (53002563378229/100000000000000 : ℝ)^65
        have hw : |(6008371131/10000000000 : ℝ)|=(6008371131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(483491193/1250000000 : ℝ)|^81 ≤ (30615038803239/100000000000000 : ℝ)^65
        have hw : |(483491193/1250000000 : ℝ)|=(483491193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(585466667/2500000000 : ℝ)|^81 ≤ (16382397806791/100000000000000 : ℝ)^65
        have hw : |(585466667/2500000000 : ℝ)|=(585466667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s2_s2_21 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-129124267/2000000000 : ℝ)*x 0 + (5762057633/10000000000 : ℝ)*x 1 + (2700096513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (129124267/2000000000 : ℝ)^81 ≤ (3288890013071/100000000000000 : ℝ)^65 := by
    have hnat : (129124267 : ℕ)^81*100000000000000^65 ≤ 3288890013071^65*2000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129124267 2000000000 3288890013071 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5762057633/10000000000 : ℝ)^81 ≤ (10061734384097/20000000000000 : ℝ)^65 := by
    have hnat : (5762057633 : ℕ)^81*20000000000000^65 ≤ 10061734384097^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5762057633 10000000000 10061734384097 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2700096513/5000000000 : ℝ)^81 ≤ (23201219025719/50000000000000 : ℝ)^65 := by
    have hnat : (2700096513 : ℕ)^81*50000000000000^65 ≤ 23201219025719^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700096513 5000000000 23201219025719 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-129124267/2000000000 : ℝ), (5762057633/10000000000 : ℝ), (2700096513/5000000000 : ℝ)] ![(3288890013071/100000000000000 : ℝ), (10061734384097/20000000000000 : ℝ), (23201219025719/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-129124267/2000000000 : ℝ)|^81 ≤ (3288890013071/100000000000000 : ℝ)^65
        have hw : |(-129124267/2000000000 : ℝ)|=(129124267/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5762057633/10000000000 : ℝ)|^81 ≤ (10061734384097/20000000000000 : ℝ)^65
        have hw : |(5762057633/10000000000 : ℝ)|=(5762057633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2700096513/5000000000 : ℝ)|^81 ≤ (23201219025719/50000000000000 : ℝ)^65
        have hw : |(2700096513/5000000000 : ℝ)|=(2700096513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s2_s2_22 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3042087403/5000000000 : ℝ)*x 0 + (-80498893/1250000000 : ℝ)*x 1 + (5069098869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3042087403/5000000000 : ℝ)^81 ≤ (10767430901619/20000000000000 : ℝ)^65 := by
    have hnat : (3042087403 : ℕ)^81*20000000000000^65 ≤ 10767430901619^65*5000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3042087403 5000000000 10767430901619 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (80498893/1250000000 : ℝ)^81 ≤ (1639272315219/50000000000000 : ℝ)^65 := by
    have hnat : (80498893 : ℕ)^81*50000000000000^65 ≤ 1639272315219^65*1250000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80498893 1250000000 1639272315219 50000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5069098869/10000000000 : ℝ)^81 ≤ (8576860169223/20000000000000 : ℝ)^65 := by
    have hnat : (5069098869 : ℕ)^81*20000000000000^65 ≤ 8576860169223^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5069098869 10000000000 8576860169223 20000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3042087403/5000000000 : ℝ), (-80498893/1250000000 : ℝ), (5069098869/10000000000 : ℝ)] ![(10767430901619/20000000000000 : ℝ), (1639272315219/50000000000000 : ℝ), (8576860169223/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3042087403/5000000000 : ℝ)|^81 ≤ (10767430901619/20000000000000 : ℝ)^65
        have hw : |(3042087403/5000000000 : ℝ)|=(3042087403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-80498893/1250000000 : ℝ)|^81 ≤ (1639272315219/50000000000000 : ℝ)^65
        have hw : |(-80498893/1250000000 : ℝ)|=(80498893/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5069098869/10000000000 : ℝ)|^81 ≤ (8576860169223/20000000000000 : ℝ)^65
        have hw : |(5069098869/10000000000 : ℝ)|=(5069098869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s2_s2_23 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (29102643/62500000 : ℝ)*x 0 + (190656051/312500000 : ℝ)*x 1 + (-1237516231/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (29102643/62500000 : ℝ)^81 ≤ (38578224818039/100000000000000 : ℝ)^65 := by
    have hnat : (29102643 : ℕ)^81*100000000000000^65 ≤ 38578224818039^65*62500000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      29102643 62500000 38578224818039 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (190656051/312500000 : ℝ)^81 ≤ (54022676494593/100000000000000 : ℝ)^65 := by
    have hnat : (190656051 : ℕ)^81*100000000000000^65 ≤ 54022676494593^65*312500000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      190656051 312500000 54022676494593 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1237516231/10000000000 : ℝ)^81 ≤ (7399098664441/100000000000000 : ℝ)^65 := by
    have hnat : (1237516231 : ℕ)^81*100000000000000^65 ≤ 7399098664441^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1237516231 10000000000 7399098664441 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(29102643/62500000 : ℝ), (190656051/312500000 : ℝ), (-1237516231/10000000000 : ℝ)] ![(38578224818039/100000000000000 : ℝ), (54022676494593/100000000000000 : ℝ), (7399098664441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(29102643/62500000 : ℝ)|^81 ≤ (38578224818039/100000000000000 : ℝ)^65
        have hw : |(29102643/62500000 : ℝ)|=(29102643/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(190656051/312500000 : ℝ)|^81 ≤ (54022676494593/100000000000000 : ℝ)^65
        have hw : |(190656051/312500000 : ℝ)|=(190656051/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1237516231/10000000000 : ℝ)|^81 ≤ (7399098664441/100000000000000 : ℝ)^65
        have hw : |(-1237516231/10000000000 : ℝ)|=(1237516231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c320063_s2_s2_27 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ)) (x : Fin 3 → ℝ) :
    (309089369/500000000 : ℝ)*x 0 + (773652779/2500000000 : ℝ)*x 1 + (2956027369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (309089369/500000000 : ℝ)^81 ≤ (54915632111843/100000000000000 : ℝ)^65 := by
    have hnat : (309089369 : ℕ)^81*100000000000000^65 ≤ 54915632111843^65*500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309089369 500000000 54915632111843 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (773652779/2500000000 : ℝ)^81 ≤ (23185518306991/100000000000000 : ℝ)^65 := by
    have hnat : (773652779 : ℕ)^81*100000000000000^65 ≤ 23185518306991^65*2500000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773652779 2500000000 23185518306991 100000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2956027369/10000000000 : ℝ)^81 ≤ (2189884956331/10000000000000 : ℝ)^65 := by
    have hnat : (2956027369 : ℕ)^81*10000000000000^65 ≤ 2189884956331^65*10000000000^81 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2956027369 10000000000 2189884956331 10000000000000 81 65 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (81/16 : ℝ)) 81 65 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(309089369/500000000 : ℝ), (773652779/2500000000 : ℝ), (2956027369/10000000000 : ℝ)] ![(54915632111843/100000000000000 : ℝ), (23185518306991/100000000000000 : ℝ), (2189884956331/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(309089369/500000000 : ℝ)|^81 ≤ (54915632111843/100000000000000 : ℝ)^65
        have hw : |(309089369/500000000 : ℝ)|=(309089369/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(773652779/2500000000 : ℝ)|^81 ≤ (23185518306991/100000000000000 : ℝ)^65
        have hw : |(773652779/2500000000 : ℝ)|=(773652779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2956027369/10000000000 : ℝ)|^81 ≤ (2189884956331/10000000000000 : ℝ)^65
        have hw : |(2956027369/10000000000 : ℝ)|=(2956027369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c320063_s2 (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((12407/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12407/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(251/500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(251/500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48013/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(48013/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((30369/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30369/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7703/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7703/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14751/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(14751/50000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (80273/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (80273/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
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
  have s2_pow0 : (12407/25000 : ℝ) ^ (5 : ℝ) ≤ (3010466978092090151/100000000000000000000 : ℝ) := by
    have hpowers : (12407/25000 : ℝ)^5 ≤ (3010466978092090151/100000000000000000000 : ℝ)^1 := by
      have hnat : (12407 : ℕ)^5*100000000000000000000^1 ≤ 3010466978092090151^1*25000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12407 25000 3010466978092090151 100000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12407/25000 : ℝ)) (X := (3010466978092090151/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s2_corner0a : (103010466978092090151/100000000000000000000 : ℝ) ≤ (5029748566480663/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (103010466978092090151/100000000000000000000 : ℝ)^1 ≤ (5029748566480663/5000000000000000 : ℝ)^5 := by
      have hnat : (103010466978092090151 : ℕ)^1*5000000000000000^5 ≤ 5029748566480663^5*100000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        103010466978092090151 100000000000000000000 5029748566480663 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5029748566480663/5000000000000000 : ℝ)) (X := (103010466978092090151/100000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s2_corner0b : (53010466978092090151/50000000000000000000 : ℝ) ≤ (1011761909360899/1000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (53010466978092090151/50000000000000000000 : ℝ)^1 ≤ (1011761909360899/1000000000000000 : ℝ)^5 := by
      have hnat : (53010466978092090151 : ℕ)^1*1000000000000000^5 ≤ 1011761909360899^5*50000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53010466978092090151 50000000000000000000 1011761909360899 1000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1011761909360899/1000000000000000 : ℝ)) (X := (53010466978092090151/50000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(29748566480663/2481400000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(3632622540479/310175000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (12407/25000 : ℝ)) (alpha := (29748566480663/2481400000000000 : ℝ)) (beta := (3632622540479/310175000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (12407/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(29748566480663/2481400000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(3632622540479/310175000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (251/500 : ℝ) ^ (5 : ℝ) ≤ (996250626251/31250000000000 : ℝ) := by
    have hpowers : (251/500 : ℝ)^5 ≤ (996250626251/31250000000000 : ℝ)^1 := by
      have hnat : (251 : ℕ)^5*31250000000000^1 ≤ 996250626251^1*500^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        251 500 996250626251 31250000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (251/500 : ℝ)) (X := (996250626251/31250000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s2_corner1a : (32246250626251/31250000000000 : ℝ) ≤ (2012592437011111/2000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (32246250626251/31250000000000 : ℝ)^1 ≤ (2012592437011111/2000000000000000 : ℝ)^5 := by
      have hnat : (32246250626251 : ℕ)^1*2000000000000000^5 ≤ 2012592437011111^5*31250000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32246250626251 31250000000000 2012592437011111 2000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2012592437011111/2000000000000000 : ℝ)) (X := (32246250626251/31250000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s2_corner1b : (16621250626251/15625000000000 : ℝ) ≤ (10124386928045399/10000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (16621250626251/15625000000000 : ℝ)^1 ≤ (10124386928045399/10000000000000000 : ℝ)^5 := by
      have hnat : (16621250626251 : ℕ)^1*10000000000000000^5 ≤ 10124386928045399^5*15625000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16621250626251 15625000000000 10124386928045399 10000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10124386928045399/10000000000000000 : ℝ)) (X := (16621250626251/15625000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(12592437011111/1004000000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(15356185747461/1255000000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (251/500 : ℝ)) (alpha := (12592437011111/1004000000000000 : ℝ)) (beta := (15356185747461/1255000000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (251/500 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(12592437011111/1004000000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(15356185747461/1255000000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (48013/100000 : ℝ) ^ (5 : ℝ) ≤ (2551492019911057351/100000000000000000000 : ℝ) := by
    have hpowers : (48013/100000 : ℝ)^5 ≤ (2551492019911057351/100000000000000000000 : ℝ)^1 := by
      have hnat : (48013 : ℕ)^5*100000000000000000000^1 ≤ 2551492019911057351^1*100000^5 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48013 100000 2551492019911057351 100000000000000000000 5 1 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (48013/100000 : ℝ)) (X := (2551492019911057351/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s2_corner2a : (102551492019911057351/100000000000000000000 : ℝ) ≤ (5025258432409507/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (102551492019911057351/100000000000000000000 : ℝ)^1 ≤ (5025258432409507/5000000000000000 : ℝ)^5 := by
      have hnat : (102551492019911057351 : ℕ)^1*5000000000000000^5 ≤ 5025258432409507^5*100000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102551492019911057351 100000000000000000000 5025258432409507 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5025258432409507/5000000000000000 : ℝ)) (X := (102551492019911057351/100000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have s2_corner2b : (52551492019911057351/50000000000000000000 : ℝ) ≤ (5050019017944361/5000000000000000 : ℝ) ^ (5 : ℝ) := by
    have hpowers : (52551492019911057351/50000000000000000000 : ℝ)^1 ≤ (5050019017944361/5000000000000000 : ℝ)^5 := by
      have hnat : (52551492019911057351 : ℕ)^1*5000000000000000^5 ≤ 5050019017944361^5*50000000000000000000^1 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52551492019911057351 50000000000000000000 5050019017944361 5000000000000000 1 5 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5050019017944361/5000000000000000 : ℝ)) (X := (52551492019911057351/50000000000000000000 : ℝ)) (by norm_num) 5 1 (by norm_num) hpowers
    simpa only [Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,div_one] using h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(25258432409507/2400650000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(12380292767427/1200325000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (5 : ℝ)) (rho := (48013/100000 : ℝ)) (alpha := (25258432409507/2400650000000000 : ℝ)) (beta := (12380292767427/1200325000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (48013/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(25258432409507/2400650000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(12380292767427/1200325000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-1339644187/10000000000 : ℝ)*X 0 0+(668249249/1250000000 : ℝ)*X 0 1+(5363475179/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((1336627901/2500000000 : ℝ)*X 1 0+(-1343910967/10000000000 : ℝ)*X 1 1+(334995249/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((5360194039/10000000000 : ℝ)*X 2 0+(1071466277/2000000000 : ℝ)*X 2 1+(-1328305433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((4146952889/10000000000 : ℝ)*X 0 0+(4144496449/10000000000 : ℝ)*X 0 1+(4132110101/10000000000 : ℝ)*X 0 2+(4146952889/10000000000 : ℝ)*X 1 0+(4144496449/10000000000 : ℝ)*X 1 1+(4132110101/10000000000 : ℝ)*X 1 2+(4146952889/10000000000 : ℝ)*X 2 0+(4144496449/10000000000 : ℝ)*X 2 1+(4132110101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-313971919/2500000000 : ℝ)*X 0 0+(36620239/78125000 : ℝ)*X 0 1+(6059532669/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((2532457261/5000000000 : ℝ)*X 1 0+(-87422903/1250000000 : ℝ)*X 1 1+(6055959433/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((2432990493/5000000000 : ℝ)*X 2 0+(1564576941/2500000000 : ℝ)*X 2 1+(-675926457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((4478051281/10000000000 : ℝ)*X 0 0+(546878849/1000000000 : ℝ)*X 0 1+(1155656549/5000000000 : ℝ)*X 0 2+(4478051281/10000000000 : ℝ)*X 1 0+(546878849/1000000000 : ℝ)*X 1 1+(1155656549/5000000000 : ℝ)*X 1 2+(4478051281/10000000000 : ℝ)*X 2 0+(546878849/1000000000 : ℝ)*X 2 1+(1155656549/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-139804007/2000000000 : ℝ)*X 0 0+(5072990411/10000000000 : ℝ)*X 0 1+(6048441903/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((1176402847/2500000000 : ℝ)*X 1 0+(-1252273237/10000000000 : ℝ)*X 1 1+(604486797/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((1511137529/2500000000 : ℝ)*X 2 0+(2542201689/5000000000 : ℝ)*X 2 1+(-343509213/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((6008371131/10000000000 : ℝ)*X 0 0+(483491193/1250000000 : ℝ)*X 0 1+(585466667/2500000000 : ℝ)*X 0 2+(6008371131/10000000000 : ℝ)*X 1 0+(483491193/1250000000 : ℝ)*X 1 1+(585466667/2500000000 : ℝ)*X 1 2+(6008371131/10000000000 : ℝ)*X 2 0+(483491193/1250000000 : ℝ)*X 2 1+(585466667/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-129124267/2000000000 : ℝ)*X 0 0+(5762057633/10000000000 : ℝ)*X 0 1+(2700096513/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((3042087403/5000000000 : ℝ)*X 1 0+(-80498893/1250000000 : ℝ)*X 1 1+(5069098869/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((29102643/62500000 : ℝ)*X 2 0+(190656051/312500000 : ℝ)*X 2 1+(-1237516231/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((309089369/500000000 : ℝ)*X 0 0+(773652779/2500000000 : ℝ)*X 0 1+(2956027369/10000000000 : ℝ)*X 0 2+(309089369/500000000 : ℝ)*X 1 0+(773652779/2500000000 : ℝ)*X 1 1+(2956027369/10000000000 : ℝ)*X 1 2+(309089369/500000000 : ℝ)*X 2 0+(773652779/2500000000 : ℝ)*X 2 1+(2956027369/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c320063_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((30369/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30369/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1244718666843402884071285053351/78694747390000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1496519/500000000000 : ℝ)*(base50) + (78968515869/500000000000 : ℝ)*(base60) + (5060394263623/1000000000000 : ℝ)*(major_s2_0) + (5060394263623/1000000000000 : ℝ)*(major_s2_1) + (5060394263623/1000000000000 : ℝ)*(major_s2_2) + (30531437/1000000000000 : ℝ)*(sp_s2_0) + (9832413/500000000000 : ℝ)*(sp_s2_6) + (928122126573/125000000000 : ℝ)*(sp_s2_7) + (3712481851477/500000000000 : ℝ)*(sp_s2_8) + (3712477207949/500000000000 : ℝ)*(sp_s2_9) + (539138860943/200000000000 : ℝ)*(sp_s2_13) + (61741329/1000000000000 : ℝ)*(sp_s2_14) + (26395599/250000000000 : ℝ)*(sp_s2_15) + (28717363/250000000000 : ℝ)*(sp_s2_23) + (2695713969541/1000000000000 : ℝ)*(f.failure) + (148501385707/20000000000 : ℝ)*(f.sum) + (10677278414326227331/48205052000000000000000000000000 : ℝ)*base62 + (916035870547167/2400650000000000000000000000 : ℝ)*base65 + (572690632910203/1255000000000000000000000000 : ℝ)*base67 + (78732939408159/600162500000000000000000000 : ℝ)*base69 + (1557028953773828247/6270497800000000000000000000000 : ℝ)*base71 + (26272779903851/155087500000000000000000000 : ℝ)*base73 + (3710007351647/1004000000000000000000000000 : ℝ)*base74 + (615861886447649/2481400000000000000000000000 : ℝ)*base77 + (5229488954088936021/15570785000000000000000000000000 : ℝ)*base79 + (1587/2500000000000000 : ℝ)*base86 + (1587/2500000000000000 : ℝ)*base88 + (1587/2500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7703/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7703/25000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (256046547594988382610298096257/78694747390000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1174443/1000000000000 : ℝ)*(base60) + (5142972648029/1000000000000 : ℝ)*(major_s2_0) + (5142972648029/1000000000000 : ℝ)*(major_s2_1) + (5142972648029/1000000000000 : ℝ)*(major_s2_2) + (17193003/1000000000000 : ℝ)*(sp_s2_0) + (23127717/1000000000000 : ℝ)*(sp_s2_1) + (3329139/125000000000 : ℝ)*(sp_s2_2) + (1815161/200000000000 : ℝ)*(sp_s2_7) + (11324211/1000000000000 : ℝ)*(sp_s2_8) + (754621378329/100000000000 : ℝ)*(sp_s2_14) + (754620560017/100000000000 : ℝ)*(sp_s2_15) + (3773106709493/500000000000 : ℝ)*(sp_s2_16) + (2739677891487/1000000000000 : ℝ)*(sp_s2_20) + (5253583/200000000000 : ℝ)*(sp_s2_27) + (1369852079701/500000000000 : ℝ)*(f.failure) + (3773120026049/500000000000 : ℝ)*(f.sum) + (10696115497731590113/48205052000000000000000000000000 : ℝ)*base62 + (45340265180961/600162500000000000000000000 : ℝ)*base64 + (218672138422131/1255000000000000000000000000 : ℝ)*base66 + (246255595790413/600162500000000000000000000 : ℝ)*base68 + (705284598999307921/6270497800000000000000000000000 : ℝ)*base71 + (35813513979547/155087500000000000000000000 : ℝ)*base72 + (219604937346181/1004000000000000000000000000 : ℝ)*base74 + (560352853230213/2481400000000000000000000000 : ℝ)*base76 + (601655029689657117/15570785000000000000000000000000 : ℝ)*base78 + (543/1250000000000000 : ℝ)*base87 + (543/1250000000000000 : ℝ)*base89 + (543/1250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14751/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(14751/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (443803713215382632100199411503/78694747390000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1593309/200000000000 : ℝ)*(base15) + (45441392843/200000000000 : ℝ)*(base40) + (4727840366309/1000000000000 : ℝ)*(major_s2_0) + (4727840366309/1000000000000 : ℝ)*(major_s2_1) + (4727840366309/1000000000000 : ℝ)*(major_s2_2) + (40368069/1000000000000 : ℝ)*(sp_s2_0) + (42444571/1000000000000 : ℝ)*(sp_s2_1) + (7182541/250000000000 : ℝ)*(sp_s2_2) + (17346453/1000000000000 : ℝ)*(sp_s2_9) + (16016873/1000000000000 : ℝ)*(sp_s2_20) + (6937078732763/1000000000000 : ℝ)*(sp_s2_21) + (1734267172429/250000000000 : ℝ)*(sp_s2_22) + (3468536512107/500000000000 : ℝ)*(sp_s2_23) + (2518543735049/1000000000000 : ℝ)*(sp_s2_27) + (1259279875961/500000000000 : ℝ)*(f.failure) + (216784971901/31250000000 : ℝ)*(f.sum) + (9567265771650185927/48205052000000000000000000000000 : ℝ)*base63 + (1199854982132391/2400650000000000000000000000 : ℝ)*base65 + (628902869724449/1255000000000000000000000000 : ℝ)*base67 + (369970850700517/600162500000000000000000000 : ℝ)*base69 + (489107708241161159/6270497800000000000000000000000 : ℝ)*base70 + (392537321882067/620350000000000000000000000 : ℝ)*base73 + (1097211736816499/1004000000000000000000000000 : ℝ)*base75 + (2276243543364227/2481400000000000000000000000 : ℝ)*base77 + (2739985222817186943/15570785000000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (1277/1250000000000000 : ℝ)*base86 + (1277/1250000000000000 : ℝ)*base88 + (1277/1250000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (5 : ℝ) ≤ p) (hpb : p ≤ (81/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (4693/2500 : ℝ) (1059/625 : ℝ) (80273/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((12407/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(12407/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(251/500 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(251/500 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48013/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(48013/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((30369/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(30369/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7703/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(7703/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(14751/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(14751/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c320063_s2 p hpa hpb X hX hprev1

#print axioms solution
