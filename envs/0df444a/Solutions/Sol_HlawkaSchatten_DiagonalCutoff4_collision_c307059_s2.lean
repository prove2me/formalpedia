-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c307059_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:14:53.489684+00:00
-- url     : https://prove2.me/submissions/5cc2bf28-8846-4ed0-8dee-ca16287e5222

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
theorem collision_support_c307059_s2_s2_2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3183739779/5000000000 : ℝ)*x 0 + (1073782887/2000000000 : ℝ)*x 1 + (-50287799/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3183739779/5000000000 : ℝ)^17 ≤ (27708938560673/50000000000000 : ℝ)^13 := by
    have hnat : (3183739779 : ℕ)^17*50000000000000^13 ≤ 27708938560673^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3183739779 5000000000 27708938560673 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1073782887/2000000000 : ℝ)^17 ≤ (44337850135857/100000000000000 : ℝ)^13 := by
    have hnat : (1073782887 : ℕ)^17*100000000000000^13 ≤ 44337850135857^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073782887 2000000000 44337850135857 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50287799/5000000000 : ℝ)^17 ≤ (122136360227/50000000000000 : ℝ)^13 := by
    have hnat : (50287799 : ℕ)^17*50000000000000^13 ≤ 122136360227^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50287799 5000000000 122136360227 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3183739779/5000000000 : ℝ), (1073782887/2000000000 : ℝ), (-50287799/5000000000 : ℝ)] ![(27708938560673/50000000000000 : ℝ), (44337850135857/100000000000000 : ℝ), (122136360227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3183739779/5000000000 : ℝ)|^17 ≤ (27708938560673/50000000000000 : ℝ)^13
        have hw : |(3183739779/5000000000 : ℝ)|=(3183739779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1073782887/2000000000 : ℝ)|^17 ≤ (44337850135857/100000000000000 : ℝ)^13
        have hw : |(1073782887/2000000000 : ℝ)|=(1073782887/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-50287799/5000000000 : ℝ)|^17 ≤ (122136360227/50000000000000 : ℝ)^13
        have hw : |(-50287799/5000000000 : ℝ)|=(50287799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307059_s2_s2_6 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3733534621/10000000000 : ℝ)*x 0 + (5899188999/10000000000 : ℝ)*x 1 + (634391459/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3733534621/10000000000 : ℝ)^17 ≤ (3446472896953/12500000000000 : ℝ)^13 := by
    have hnat : (3733534621 : ℕ)^17*12500000000000^13 ≤ 3446472896953^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3733534621 10000000000 3446472896953 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5899188999/10000000000 : ℝ)^17 ≤ (50149530027187/100000000000000 : ℝ)^13 := by
    have hnat : (5899188999 : ℕ)^17*100000000000000^13 ≤ 50149530027187^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5899188999 10000000000 50149530027187 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (634391459/2000000000 : ℝ)^17 ≤ (22278686771219/100000000000000 : ℝ)^13 := by
    have hnat : (634391459 : ℕ)^17*100000000000000^13 ≤ 22278686771219^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634391459 2000000000 22278686771219 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3733534621/10000000000 : ℝ), (5899188999/10000000000 : ℝ), (634391459/2000000000 : ℝ)] ![(3446472896953/12500000000000 : ℝ), (50149530027187/100000000000000 : ℝ), (22278686771219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3733534621/10000000000 : ℝ)|^17 ≤ (3446472896953/12500000000000 : ℝ)^13
        have hw : |(3733534621/10000000000 : ℝ)|=(3733534621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5899188999/10000000000 : ℝ)|^17 ≤ (50149530027187/100000000000000 : ℝ)^13
        have hw : |(5899188999/10000000000 : ℝ)|=(5899188999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(634391459/2000000000 : ℝ)|^17 ≤ (22278686771219/100000000000000 : ℝ)^13
        have hw : |(634391459/2000000000 : ℝ)|=(634391459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307059_s2_s2_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2173640711/10000000000 : ℝ)*x 0 + (438222497/2500000000 : ℝ)*x 1 + (405963827/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2173640711/10000000000 : ℝ)^17 ≤ (3397703991743/25000000000000 : ℝ)^13 := by
    have hnat : (2173640711 : ℕ)^17*25000000000000^13 ≤ 3397703991743^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2173640711 10000000000 3397703991743 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (438222497/2500000000 : ℝ)^17 ≤ (10258025793981/100000000000000 : ℝ)^13 := by
    have hnat : (438222497 : ℕ)^17*100000000000000^13 ≤ 10258025793981^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438222497 2500000000 10258025793981 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (405963827/500000000 : ℝ)^17 ≤ (76151158226757/100000000000000 : ℝ)^13 := by
    have hnat : (405963827 : ℕ)^17*100000000000000^13 ≤ 76151158226757^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      405963827 500000000 76151158226757 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2173640711/10000000000 : ℝ), (438222497/2500000000 : ℝ), (405963827/500000000 : ℝ)] ![(3397703991743/25000000000000 : ℝ), (10258025793981/100000000000000 : ℝ), (76151158226757/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2173640711/10000000000 : ℝ)|^17 ≤ (3397703991743/25000000000000 : ℝ)^13
        have hw : |(-2173640711/10000000000 : ℝ)|=(2173640711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(438222497/2500000000 : ℝ)|^17 ≤ (10258025793981/100000000000000 : ℝ)^13
        have hw : |(438222497/2500000000 : ℝ)|=(438222497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(405963827/500000000 : ℝ)|^17 ≤ (76151158226757/100000000000000 : ℝ)^13
        have hw : |(405963827/500000000 : ℝ)|=(405963827/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307059_s2_s2_8 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (227749681/1000000000 : ℝ)*x 0 + (-1635874547/10000000000 : ℝ)*x 1 + (8121787287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (227749681/1000000000 : ℝ)^17 ≤ (577846476429/4000000000000 : ℝ)^13 := by
    have hnat : (227749681 : ℕ)^17*4000000000000^13 ≤ 577846476429^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227749681 1000000000 577846476429 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1635874547/10000000000 : ℝ)^17 ≤ (585742766513/6250000000000 : ℝ)^13 := by
    have hnat : (1635874547 : ℕ)^17*6250000000000^13 ≤ 585742766513^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1635874547 10000000000 585742766513 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8121787287/10000000000 : ℝ)^17 ≤ (76181953804801/100000000000000 : ℝ)^13 := by
    have hnat : (8121787287 : ℕ)^17*100000000000000^13 ≤ 76181953804801^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8121787287 10000000000 76181953804801 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(227749681/1000000000 : ℝ), (-1635874547/10000000000 : ℝ), (8121787287/10000000000 : ℝ)] ![(577846476429/4000000000000 : ℝ), (585742766513/6250000000000 : ℝ), (76181953804801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(227749681/1000000000 : ℝ)|^17 ≤ (577846476429/4000000000000 : ℝ)^13
        have hw : |(227749681/1000000000 : ℝ)|=(227749681/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1635874547/10000000000 : ℝ)|^17 ≤ (585742766513/6250000000000 : ℝ)^13
        have hw : |(-1635874547/10000000000 : ℝ)|=(1635874547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8121787287/10000000000 : ℝ)|^17 ≤ (76181953804801/100000000000000 : ℝ)^13
        have hw : |(8121787287/10000000000 : ℝ)|=(8121787287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307059_s2_s2_9 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (898748981/2000000000 : ℝ)*x 0 + (57456599/80000000 : ℝ)*x 1 + (-771009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (898748981/2000000000 : ℝ)^17 ≤ (1405331200251/4000000000000 : ℝ)^13 := by
    have hnat : (898748981 : ℕ)^17*4000000000000^13 ≤ 1405331200251^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898748981 2000000000 1405331200251 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (57456599/80000000 : ℝ)^17 ≤ (32433150813697/50000000000000 : ℝ)^13 := by
    have hnat : (57456599 : ℕ)^17*50000000000000^13 ≤ 32433150813697^13*80000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57456599 80000000 32433150813697 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (771009/10000000000 : ℝ)^17 ≤ (418349523/100000000000000 : ℝ)^13 := by
    have hnat : (771009 : ℕ)^17*100000000000000^13 ≤ 418349523^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      771009 10000000000 418349523 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(898748981/2000000000 : ℝ), (57456599/80000000 : ℝ), (-771009/10000000000 : ℝ)] ![(1405331200251/4000000000000 : ℝ), (32433150813697/50000000000000 : ℝ), (418349523/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(898748981/2000000000 : ℝ)|^17 ≤ (1405331200251/4000000000000 : ℝ)^13
        have hw : |(898748981/2000000000 : ℝ)|=(898748981/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(57456599/80000000 : ℝ)|^17 ≤ (32433150813697/50000000000000 : ℝ)^13
        have hw : |(57456599/80000000 : ℝ)|=(57456599/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-771009/10000000000 : ℝ)|^17 ≤ (418349523/100000000000000 : ℝ)^13
        have hw : |(-771009/10000000000 : ℝ)|=(771009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307059_s2_s2_13 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2369807439/10000000000 : ℝ)*x 0 + (7934271757/10000000000 : ℝ)*x 1 + (57353671/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2369807439/10000000000 : ℝ)^17 ≤ (15216580798373/100000000000000 : ℝ)^13 := by
    have hnat : (2369807439 : ℕ)^17*100000000000000^13 ≤ 15216580798373^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2369807439 10000000000 15216580798373 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7934271757/10000000000 : ℝ)^17 ≤ (73890085710349/100000000000000 : ℝ)^13 := by
    have hnat : (7934271757 : ℕ)^17*100000000000000^13 ≤ 73890085710349^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7934271757 10000000000 73890085710349 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (57353671/312500000 : ℝ)^17 ≤ (2178666694897/20000000000000 : ℝ)^13 := by
    have hnat : (57353671 : ℕ)^17*20000000000000^13 ≤ 2178666694897^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      57353671 312500000 2178666694897 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2369807439/10000000000 : ℝ), (7934271757/10000000000 : ℝ), (57353671/312500000 : ℝ)] ![(15216580798373/100000000000000 : ℝ), (73890085710349/100000000000000 : ℝ), (2178666694897/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2369807439/10000000000 : ℝ)|^17 ≤ (15216580798373/100000000000000 : ℝ)^13
        have hw : |(2369807439/10000000000 : ℝ)|=(2369807439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7934271757/10000000000 : ℝ)|^17 ≤ (73890085710349/100000000000000 : ℝ)^13
        have hw : |(7934271757/10000000000 : ℝ)|=(7934271757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(57353671/312500000 : ℝ)|^17 ≤ (2178666694897/20000000000000 : ℝ)^13
        have hw : |(57353671/312500000 : ℝ)|=(57353671/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307059_s2_s2_14 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-987768137/5000000000 : ℝ)*x 0 + (1193225887/5000000000 : ℝ)*x 1 + (3916090641/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (987768137/5000000000 : ℝ)^17 ≤ (11994239135093/100000000000000 : ℝ)^13 := by
    have hnat : (987768137 : ℕ)^17*100000000000000^13 ≤ 11994239135093^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      987768137 5000000000 11994239135093 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1193225887/5000000000 : ℝ)^17 ≤ (15356489361409/100000000000000 : ℝ)^13 := by
    have hnat : (1193225887 : ℕ)^17*100000000000000^13 ≤ 15356489361409^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1193225887 5000000000 15356489361409 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3916090641/5000000000 : ℝ)^17 ≤ (7264927148369/10000000000000 : ℝ)^13 := by
    have hnat : (3916090641 : ℕ)^17*10000000000000^13 ≤ 7264927148369^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3916090641 5000000000 7264927148369 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-987768137/5000000000 : ℝ), (1193225887/5000000000 : ℝ), (3916090641/5000000000 : ℝ)] ![(11994239135093/100000000000000 : ℝ), (15356489361409/100000000000000 : ℝ), (7264927148369/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-987768137/5000000000 : ℝ)|^17 ≤ (11994239135093/100000000000000 : ℝ)^13
        have hw : |(-987768137/5000000000 : ℝ)|=(987768137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1193225887/5000000000 : ℝ)|^17 ≤ (15356489361409/100000000000000 : ℝ)^13
        have hw : |(1193225887/5000000000 : ℝ)|=(1193225887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3916090641/5000000000 : ℝ)|^17 ≤ (7264927148369/10000000000000 : ℝ)^13
        have hw : |(3916090641/5000000000 : ℝ)|=(3916090641/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307059_s2_s2_15 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1922293703/10000000000 : ℝ)*x 0 + (-1216421659/5000000000 : ℝ)*x 1 + (979325793/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1922293703/10000000000 : ℝ)^17 ≤ (1446660422919/12500000000000 : ℝ)^13 := by
    have hnat : (1922293703 : ℕ)^17*12500000000000^13 ≤ 1446660422919^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1922293703 10000000000 1446660422919 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1216421659/5000000000 : ℝ)^17 ≤ (15748028175157/100000000000000 : ℝ)^13 := by
    have hnat : (1216421659 : ℕ)^17*100000000000000^13 ≤ 15748028175157^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1216421659 5000000000 15748028175157 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (979325793/1250000000 : ℝ)^17 ≤ (72678688433111/100000000000000 : ℝ)^13 := by
    have hnat : (979325793 : ℕ)^17*100000000000000^13 ≤ 72678688433111^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979325793 1250000000 72678688433111 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1922293703/10000000000 : ℝ), (-1216421659/5000000000 : ℝ), (979325793/1250000000 : ℝ)] ![(1446660422919/12500000000000 : ℝ), (15748028175157/100000000000000 : ℝ), (72678688433111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1922293703/10000000000 : ℝ)|^17 ≤ (1446660422919/12500000000000 : ℝ)^13
        have hw : |(1922293703/10000000000 : ℝ)|=(1922293703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1216421659/5000000000 : ℝ)|^17 ≤ (15748028175157/100000000000000 : ℝ)^13
        have hw : |(-1216421659/5000000000 : ℝ)|=(1216421659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(979325793/1250000000 : ℝ)|^17 ≤ (72678688433111/100000000000000 : ℝ)^13
        have hw : |(979325793/1250000000 : ℝ)|=(979325793/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307059_s2_s2_16 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7959800349/10000000000 : ℝ)*x 0 + (3548521999/10000000000 : ℝ)*x 1 + (18991/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7959800349/10000000000 : ℝ)^17 ≤ (9275141613619/12500000000000 : ℝ)^13 := by
    have hnat : (7959800349 : ℕ)^17*12500000000000^13 ≤ 9275141613619^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7959800349 10000000000 9275141613619 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3548521999/10000000000 : ℝ)^17 ≤ (25798863785333/100000000000000 : ℝ)^13 := by
    have hnat : (3548521999 : ℕ)^17*100000000000000^13 ≤ 25798863785333^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3548521999 10000000000 25798863785333 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (18991/10000000000 : ℝ)^17 ≤ (103027/3125000000000 : ℝ)^13 := by
    have hnat : (18991 : ℕ)^17*3125000000000^13 ≤ 103027^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18991 10000000000 103027 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7959800349/10000000000 : ℝ), (3548521999/10000000000 : ℝ), (18991/10000000000 : ℝ)] ![(9275141613619/12500000000000 : ℝ), (25798863785333/100000000000000 : ℝ), (103027/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7959800349/10000000000 : ℝ)|^17 ≤ (9275141613619/12500000000000 : ℝ)^13
        have hw : |(7959800349/10000000000 : ℝ)|=(7959800349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3548521999/10000000000 : ℝ)|^17 ≤ (25798863785333/100000000000000 : ℝ)^13
        have hw : |(3548521999/10000000000 : ℝ)|=(3548521999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(18991/10000000000 : ℝ)|^17 ≤ (103027/3125000000000 : ℝ)^13
        have hw : |(18991/10000000000 : ℝ)|=(18991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307059_s2_s2_20 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6497909769/10000000000 : ℝ)*x 0 + (2052949671/5000000000 : ℝ)*x 1 + (1960030759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6497909769/10000000000 : ℝ)^17 ≤ (11381397000333/20000000000000 : ℝ)^13 := by
    have hnat : (6497909769 : ℕ)^17*20000000000000^13 ≤ 11381397000333^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6497909769 10000000000 11381397000333 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2052949671/5000000000 : ℝ)^17 ≤ (7805433249137/25000000000000 : ℝ)^13 := by
    have hnat : (2052949671 : ℕ)^17*25000000000000^13 ≤ 7805433249137^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052949671 5000000000 7805433249137 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1960030759/10000000000 : ℝ)^17 ≤ (11871281988263/100000000000000 : ℝ)^13 := by
    have hnat : (1960030759 : ℕ)^17*100000000000000^13 ≤ 11871281988263^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1960030759 10000000000 11871281988263 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6497909769/10000000000 : ℝ), (2052949671/5000000000 : ℝ), (1960030759/10000000000 : ℝ)] ![(11381397000333/20000000000000 : ℝ), (7805433249137/25000000000000 : ℝ), (11871281988263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6497909769/10000000000 : ℝ)|^17 ≤ (11381397000333/20000000000000 : ℝ)^13
        have hw : |(6497909769/10000000000 : ℝ)|=(6497909769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2052949671/5000000000 : ℝ)|^17 ≤ (7805433249137/25000000000000 : ℝ)^13
        have hw : |(2052949671/5000000000 : ℝ)|=(2052949671/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1960030759/10000000000 : ℝ)|^17 ≤ (11871281988263/100000000000000 : ℝ)^13
        have hw : |(1960030759/10000000000 : ℝ)|=(1960030759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307059_s2_s2_21 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-4244695931/10000000000 : ℝ)*x 0 + (608939811/2000000000 : ℝ)*x 1 + (693410053/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4244695931/10000000000 : ℝ)^17 ≤ (32609027115969/100000000000000 : ℝ)^13 := by
    have hnat : (4244695931 : ℕ)^17*100000000000000^13 ≤ 32609027115969^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244695931 10000000000 32609027115969 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (608939811/2000000000 : ℝ)^17 ≤ (515554997/2441406250 : ℝ)^13 := by
    have hnat : (608939811 : ℕ)^17*2441406250^13 ≤ 515554997^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      608939811 2000000000 515554997 2441406250 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (693410053/1250000000 : ℝ)^17 ≤ (46273840200859/100000000000000 : ℝ)^13 := by
    have hnat : (693410053 : ℕ)^17*100000000000000^13 ≤ 46273840200859^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      693410053 1250000000 46273840200859 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-4244695931/10000000000 : ℝ), (608939811/2000000000 : ℝ), (693410053/1250000000 : ℝ)] ![(32609027115969/100000000000000 : ℝ), (515554997/2441406250 : ℝ), (46273840200859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-4244695931/10000000000 : ℝ)|^17 ≤ (32609027115969/100000000000000 : ℝ)^13
        have hw : |(-4244695931/10000000000 : ℝ)|=(4244695931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(608939811/2000000000 : ℝ)|^17 ≤ (515554997/2441406250 : ℝ)^13
        have hw : |(608939811/2000000000 : ℝ)|=(608939811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(693410053/1250000000 : ℝ)|^17 ≤ (46273840200859/100000000000000 : ℝ)^13
        have hw : |(693410053/1250000000 : ℝ)|=(693410053/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307059_s2_s2_22 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3008056159/10000000000 : ℝ)*x 0 + (-3611914833/10000000000 : ℝ)*x 1 + (3068584743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3008056159/10000000000 : ℝ)^17 ≤ (20785407198573/100000000000000 : ℝ)^13 := by
    have hnat : (3008056159 : ℕ)^17*100000000000000^13 ≤ 20785407198573^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3008056159 10000000000 20785407198573 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3611914833/10000000000 : ℝ)^17 ≤ (26403210157571/100000000000000 : ℝ)^13 := by
    have hnat : (3611914833 : ℕ)^17*100000000000000^13 ≤ 26403210157571^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3611914833 10000000000 26403210157571 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3068584743/5000000000 : ℝ)^17 ≤ (52811382629973/100000000000000 : ℝ)^13 := by
    have hnat : (3068584743 : ℕ)^17*100000000000000^13 ≤ 52811382629973^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3068584743 5000000000 52811382629973 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3008056159/10000000000 : ℝ), (-3611914833/10000000000 : ℝ), (3068584743/5000000000 : ℝ)] ![(20785407198573/100000000000000 : ℝ), (26403210157571/100000000000000 : ℝ), (52811382629973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3008056159/10000000000 : ℝ)|^17 ≤ (20785407198573/100000000000000 : ℝ)^13
        have hw : |(3008056159/10000000000 : ℝ)|=(3008056159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3611914833/10000000000 : ℝ)|^17 ≤ (26403210157571/100000000000000 : ℝ)^13
        have hw : |(-3611914833/10000000000 : ℝ)|=(3611914833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3068584743/5000000000 : ℝ)|^17 ≤ (52811382629973/100000000000000 : ℝ)^13
        have hw : |(3068584743/5000000000 : ℝ)|=(3068584743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307059_s2_s2_23 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7964954817/10000000000 : ℝ)*x 0 + (3541779879/10000000000 : ℝ)*x 1 + (55421/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7964954817/10000000000 : ℝ)^17 ≤ (74263973612157/100000000000000 : ℝ)^13 := by
    have hnat : (7964954817 : ℕ)^17*100000000000000^13 ≤ 74263973612157^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7964954817 10000000000 74263973612157 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3541779879/10000000000 : ℝ)^17 ≤ (12867391479447/50000000000000 : ℝ)^13 := by
    have hnat : (3541779879 : ℕ)^17*50000000000000^13 ≤ 12867391479447^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3541779879 10000000000 12867391479447 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (55421/312500000 : ℝ)^17 ≤ (621707983/50000000000000 : ℝ)^13 := by
    have hnat : (55421 : ℕ)^17*50000000000000^13 ≤ 621707983^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55421 312500000 621707983 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7964954817/10000000000 : ℝ), (3541779879/10000000000 : ℝ), (55421/312500000 : ℝ)] ![(74263973612157/100000000000000 : ℝ), (12867391479447/50000000000000 : ℝ), (621707983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7964954817/10000000000 : ℝ)|^17 ≤ (74263973612157/100000000000000 : ℝ)^13
        have hw : |(7964954817/10000000000 : ℝ)|=(7964954817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3541779879/10000000000 : ℝ)|^17 ≤ (12867391479447/50000000000000 : ℝ)^13
        have hw : |(3541779879/10000000000 : ℝ)|=(3541779879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(55421/312500000 : ℝ)|^17 ≤ (621707983/50000000000000 : ℝ)^13
        have hw : |(55421/312500000 : ℝ)|=(55421/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307059_s2_s2_27 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (480361941/2500000000 : ℝ)*x 0 + (319529181/400000000 : ℝ)*x 1 + (220958947/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (480361941/2500000000 : ℝ)^17 ≤ (11566623723407/100000000000000 : ℝ)^13 := by
    have hnat : (480361941 : ℕ)^17*100000000000000^13 ≤ 11566623723407^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480361941 2500000000 11566623723407 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (319529181/400000000 : ℝ)^17 ≤ (74547882993193/100000000000000 : ℝ)^13 := by
    have hnat : (319529181 : ℕ)^17*100000000000000^13 ≤ 74547882993193^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319529181 400000000 74547882993193 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (220958947/1000000000 : ℝ)^17 ≤ (13885493262349/100000000000000 : ℝ)^13 := by
    have hnat : (220958947 : ℕ)^17*100000000000000^13 ≤ 13885493262349^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220958947 1000000000 13885493262349 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(480361941/2500000000 : ℝ), (319529181/400000000 : ℝ), (220958947/1000000000 : ℝ)] ![(11566623723407/100000000000000 : ℝ), (74547882993193/100000000000000 : ℝ), (13885493262349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(480361941/2500000000 : ℝ)|^17 ≤ (11566623723407/100000000000000 : ℝ)^13
        have hw : |(480361941/2500000000 : ℝ)|=(480361941/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(319529181/400000000 : ℝ)|^17 ≤ (74547882993193/100000000000000 : ℝ)^13
        have hw : |(319529181/400000000 : ℝ)|=(319529181/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(220958947/1000000000 : ℝ)|^17 ≤ (13885493262349/100000000000000 : ℝ)^13
        have hw : |(220958947/1000000000 : ℝ)|=(220958947/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c307059_s2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((43333/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43333/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21631/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21631/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(71817/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(71817/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3051/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3051/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(187/250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(187/250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(50893/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(50893/100000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4817/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4817/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4817/6250 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (92559/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base44 : ((-1 : ℝ)*N 1+(1 : ℝ)*P 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ptotal 1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  rcases hprev1 with ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩
  have s2_pow0 : (43333/50000 : ℝ) ^ (135/32 : ℝ) ≤ (54676338639080084377/100000000000000000000 : ℝ) := by
    have hpowers : (43333/50000 : ℝ)^135 ≤ (54676338639080084377/100000000000000000000 : ℝ)^32 := by
      have hnat : (43333 : ℕ)^135*100000000000000000000^32 ≤ 54676338639080084377^32*50000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        43333 50000 54676338639080084377 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (43333/50000 : ℝ)) (X := (54676338639080084377/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner0a : (154676338639080084377/100000000000000000000 : ℝ) ≤ (5544603316170057/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (154676338639080084377/100000000000000000000 : ℝ)^32 ≤ (5544603316170057/5000000000000000 : ℝ)^135 := by
      have hnat : (154676338639080084377 : ℕ)^32*5000000000000000^135 ≤ 5544603316170057^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        154676338639080084377 100000000000000000000 5544603316170057 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5544603316170057/5000000000000000 : ℝ)) (X := (154676338639080084377/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner0b : (104676338639080084377/50000000000000000000 : ℝ) ≤ (11914068518832213/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (104676338639080084377/50000000000000000000 : ℝ)^32 ≤ (11914068518832213/10000000000000000 : ℝ)^135 := by
      have hnat : (104676338639080084377 : ℕ)^32*10000000000000000^135 ≤ 11914068518832213^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104676338639080084377 50000000000000000000 11914068518832213 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11914068518832213/10000000000000000 : ℝ)) (X := (104676338639080084377/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(544603316170057/4333300000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(824861886492099/8666600000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (43333/50000 : ℝ)) (alpha := (544603316170057/4333300000000000 : ℝ)) (beta := (824861886492099/8666600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (43333/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(544603316170057/4333300000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(824861886492099/8666600000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (21631/25000 : ℝ) ^ (135/32 : ℝ) ≤ (54299394074465185171/100000000000000000000 : ℝ) := by
    have hpowers : (21631/25000 : ℝ)^135 ≤ (54299394074465185171/100000000000000000000 : ℝ)^32 := by
      have hnat : (21631 : ℕ)^135*100000000000000000000^32 ≤ 54299394074465185171^32*25000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        21631 25000 54299394074465185171 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (21631/25000 : ℝ)) (X := (54299394074465185171/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner1a : (154299394074465185171/100000000000000000000 : ℝ) ≤ (11082794914119321/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (154299394074465185171/100000000000000000000 : ℝ)^32 ≤ (11082794914119321/10000000000000000 : ℝ)^135 := by
      have hnat : (154299394074465185171 : ℕ)^32*10000000000000000^135 ≤ 11082794914119321^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        154299394074465185171 100000000000000000000 11082794914119321 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11082794914119321/10000000000000000 : ℝ)) (X := (154299394074465185171/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner1b : (104299394074465185171/50000000000000000000 : ℝ) ≤ (2975971221547941/2500000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (104299394074465185171/50000000000000000000 : ℝ)^32 ≤ (2975971221547941/2500000000000000 : ℝ)^135 := by
      have hnat : (104299394074465185171 : ℕ)^32*2500000000000000^135 ≤ 2975971221547941^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104299394074465185171 50000000000000000000 2975971221547941 2500000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2975971221547941/2500000000000000 : ℝ)) (X := (104299394074465185171/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(1082794914119321/8652400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(821089972072443/8652400000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (21631/25000 : ℝ)) (alpha := (1082794914119321/8652400000000000 : ℝ)) (beta := (821089972072443/8652400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (21631/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(1082794914119321/8652400000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(821089972072443/8652400000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (71817/100000 : ℝ) ^ (135/32 : ℝ) ≤ (24743364383654880539/100000000000000000000 : ℝ) := by
    have hpowers : (71817/100000 : ℝ)^135 ≤ (24743364383654880539/100000000000000000000 : ℝ)^32 := by
      have hnat : (71817 : ℕ)^135*100000000000000000000^32 ≤ 24743364383654880539^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71817 100000 24743364383654880539 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (71817/100000 : ℝ)) (X := (24743364383654880539/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner2a : (124743364383654880539/100000000000000000000 : ℝ) ≤ (10538036356336989/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (124743364383654880539/100000000000000000000 : ℝ)^32 ≤ (10538036356336989/10000000000000000 : ℝ)^135 := by
      have hnat : (124743364383654880539 : ℕ)^32*10000000000000000^135 ≤ 10538036356336989^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        124743364383654880539 100000000000000000000 10538036356336989 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10538036356336989/10000000000000000 : ℝ)) (X := (124743364383654880539/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s2_corner2b : (74743364383654880539/50000000000000000000 : ℝ) ≤ (10999863401552449/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (74743364383654880539/50000000000000000000 : ℝ)^32 ≤ (10999863401552449/10000000000000000 : ℝ)^135 := by
      have hnat : (74743364383654880539 : ℕ)^32*10000000000000000^135 ≤ 10999863401552449^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        74743364383654880539 50000000000000000000 10999863401552449 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10999863401552449/10000000000000000 : ℝ)) (X := (74743364383654880539/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(538036356336989/7181700000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(23091352260773/359085000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (71817/100000 : ℝ)) (alpha := (538036356336989/7181700000000000 : ℝ)) (beta := (23091352260773/359085000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (71817/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(538036356336989/7181700000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(23091352260773/359085000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_2 : ((3183739779/5000000000 : ℝ)*X 2 0+(1073782887/2000000000 : ℝ)*X 2 1+(-50287799/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307059_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_6 : ((3733534621/10000000000 : ℝ)*X 0 0+(5899188999/10000000000 : ℝ)*X 0 1+(634391459/2000000000 : ℝ)*X 0 2+(3733534621/10000000000 : ℝ)*X 1 0+(5899188999/10000000000 : ℝ)*X 1 1+(634391459/2000000000 : ℝ)*X 1 2+(3733534621/10000000000 : ℝ)*X 2 0+(5899188999/10000000000 : ℝ)*X 2 1+(634391459/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307059_s2_s2_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-2173640711/10000000000 : ℝ)*X 0 0+(438222497/2500000000 : ℝ)*X 0 1+(405963827/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307059_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((227749681/1000000000 : ℝ)*X 1 0+(-1635874547/10000000000 : ℝ)*X 1 1+(8121787287/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307059_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((898748981/2000000000 : ℝ)*X 2 0+(57456599/80000000 : ℝ)*X 2 1+(-771009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307059_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((2369807439/10000000000 : ℝ)*X 0 0+(7934271757/10000000000 : ℝ)*X 0 1+(57353671/312500000 : ℝ)*X 0 2+(2369807439/10000000000 : ℝ)*X 1 0+(7934271757/10000000000 : ℝ)*X 1 1+(57353671/312500000 : ℝ)*X 1 2+(2369807439/10000000000 : ℝ)*X 2 0+(7934271757/10000000000 : ℝ)*X 2 1+(57353671/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307059_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-987768137/5000000000 : ℝ)*X 0 0+(1193225887/5000000000 : ℝ)*X 0 1+(3916090641/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307059_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((1922293703/10000000000 : ℝ)*X 1 0+(-1216421659/5000000000 : ℝ)*X 1 1+(979325793/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307059_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((7959800349/10000000000 : ℝ)*X 2 0+(3548521999/10000000000 : ℝ)*X 2 1+(18991/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307059_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((6497909769/10000000000 : ℝ)*X 0 0+(2052949671/5000000000 : ℝ)*X 0 1+(1960030759/10000000000 : ℝ)*X 0 2+(6497909769/10000000000 : ℝ)*X 1 0+(2052949671/5000000000 : ℝ)*X 1 1+(1960030759/10000000000 : ℝ)*X 1 2+(6497909769/10000000000 : ℝ)*X 2 0+(2052949671/5000000000 : ℝ)*X 2 1+(1960030759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307059_s2_s2_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((-4244695931/10000000000 : ℝ)*X 0 0+(608939811/2000000000 : ℝ)*X 0 1+(693410053/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307059_s2_s2_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((3008056159/10000000000 : ℝ)*X 1 0+(-3611914833/10000000000 : ℝ)*X 1 1+(3068584743/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307059_s2_s2_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_23 : ((7964954817/10000000000 : ℝ)*X 2 0+(3541779879/10000000000 : ℝ)*X 2 1+(55421/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307059_s2_s2_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_27 : ((480361941/2500000000 : ℝ)*X 0 0+(319529181/400000000 : ℝ)*X 0 1+(220958947/1000000000 : ℝ)*X 0 2+(480361941/2500000000 : ℝ)*X 1 0+(319529181/400000000 : ℝ)*X 1 1+(220958947/1000000000 : ℝ)*X 1 2+(480361941/2500000000 : ℝ)*X 2 0+(319529181/400000000 : ℝ)*X 2 1+(220958947/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307059_s2_s2_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((3051/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3051/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (253783225573445021057358951/37493444920000000000000000000000 : ℝ) := by norm_num
    linear_combination (158166918149/200000000000 : ℝ)*(base7) + (155487/1000000000000 : ℝ)*(base53) + (4720857491/50000000000 : ℝ)*(base60) + (402651975339/200000000000 : ℝ)*(major_s2_0) + (402651975339/200000000000 : ℝ)*(major_s2_1) + (251657465151/125000000000 : ℝ)*(major_s2_2) + (2507547/500000000000 : ℝ)*(sp_s2_2) + (1121683240253/500000000000 : ℝ)*(sp_s2_7) + (448672777283/200000000000 : ℝ)*(sp_s2_8) + (1121693052341/500000000000 : ℝ)*(sp_s2_9) + (2085945486367/1000000000000 : ℝ)*(sp_s2_13) + (24483783/1000000000000 : ℝ)*(sp_s2_14) + (13538937/500000000000 : ℝ)*(sp_s2_15) + (1154459/50000000000 : ℝ)*(sp_s2_27) + (647566992401/500000000000 : ℝ)*(f.failure) + (70105972493/31250000000 : ℝ)*(f.sum) + (52749861627467484491/207129803600000000000000000000000 : ℝ)*base62 + (1791721697697/47878000000000000000000000 : ℝ)*base65 + (354408760315417/1730480000000000000000000000 : ℝ)*base67 + (68304626107073/1196950000000000000000000000 : ℝ)*base69 + (245894489056841059/829878949600000000000000000000 : ℝ)*base70 + (344404415983341/1733320000000000000000000000 : ℝ)*base73 + (593966435567659/1730480000000000000000000000 : ℝ)*base75 + (122827759259629/866660000000000000000000000 : ℝ)*base77 + (3969791914166820507/74986889840000000000000000000000 : ℝ)*base79 + (81/6250000000000000 : ℝ)*base87 + (81/6250000000000000 : ℝ)*base89 + (81/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(187/250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(187/250 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2731376639787086274117/433330000000000000000000000 : ℝ) := by norm_num
    linear_combination (768897287863/1000000000000 : ℝ)*(base7) + (34263/25000000000 : ℝ)*(base13) + (15239/62500000000 : ℝ)*(base40) + (1809427/1000000000000 : ℝ)*(base59) + (21457345677/125000000000 : ℝ)*(base60) + (1177708958149/500000000000 : ℝ)*(major_s2_0) + (1177708958149/500000000000 : ℝ)*(major_s2_1) + (1177708958149/500000000000 : ℝ)*(major_s2_2) + (32740463/1000000000000 : ℝ)*(sp_s2_7) + (680274736137/250000000000 : ℝ)*(sp_s2_14) + (680283263883/250000000000 : ℝ)*(sp_s2_15) + (2718267609533/1000000000000 : ℝ)*(sp_s2_16) + (571035550849/250000000000 : ℝ)*(sp_s2_20) + (1432722999/500000000000 : ℝ)*(sp_s2_23) + (1515244915533/1000000000000 : ℝ)*(f.failure) + (680283263883/250000000000 : ℝ)*(f.sum) + (6657560988794825531/310694705400000000000000000000000 : ℝ)*base62 + (394830560021/89771250000000000000000000 : ℝ)*base64 + (4416032082753607/4326200000000000000000000000 : ℝ)*base67 + (957731426952439/3590850000000000000000000000 : ℝ)*base69 + (10847047609682684521/155602303050000000000000000000000 : ℝ)*base71 + (1031932151860009/4333300000000000000000000000 : ℝ)*base72 + (3892439117030489/4326200000000000000000000000 : ℝ)*base75 + (264273847144341/270831250000000000000000000 : ℝ)*base77 + (62603155803962199487/187467224600000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (3277/12500000000000000 : ℝ)*base86 + (3277/12500000000000000 : ℝ)*base88 + (3277/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(50893/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(50893/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (590395777307565239712129559687/224388894484970000000000000000000000 : ℝ) := by norm_num
    linear_combination (228608549639/500000000000 : ℝ)*(base7) + (1144611/500000000000 : ℝ)*(base11) + (189833841179/1000000000000 : ℝ)*(base44) + (33208927999/1000000000000 : ℝ)*(base50) + (1155914304311/500000000000 : ℝ)*(major_s2_0) + (2121994767443/1000000000000 : ℝ)*(major_s2_1) + (1155914304311/500000000000 : ℝ)*(major_s2_2) + (3513471/500000000000 : ℝ)*(sp_s2_6) + (30091691/500000000000 : ℝ)*(sp_s2_13) + (1160566259/500000000000 : ℝ)*(sp_s2_16) + (2854319838361/1000000000000 : ℝ)*(sp_s2_21) + (666122071601/250000000000 : ℝ)*(sp_s2_22) + (570400199013/200000000000 : ℝ)*(sp_s2_23) + (1754519877109/1000000000000 : ℝ)*(sp_s2_27) + (743601914667/500000000000 : ℝ)*(f.failure) + (2854322127583/1000000000000 : ℝ)*(f.sum) + (26185413008249720141/621389410800000000000000000000000 : ℝ)*base62 + (60411838550573/179542500000000000000000000 : ℝ)*base64 + (4457996922323871/8652400000000000000000000000 : ℝ)*base66 + (1758041206793899/3590850000000000000000000000 : ℝ)*base68 + (21445405262214753593/77801151525000000000000000000000 : ℝ)*base70 + (2329033266318651/4333300000000000000000000000 : ℝ)*base72 + (702643810851117/8652400000000000000000000000 : ℝ)*base74 + (568812601222483/2166650000000000000000000000 : ℝ)*base76 + (142852829804719656287/374934449200000000000000000000000 : ℝ)*base78 + (6977/6250000000000000 : ℝ)*base87 + (6977/6250000000000000 : ℝ)*base89 + (6977/6250000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, true]])
    (hprev1 : (0 : ℝ) ≤ ((43333/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(43333/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(21631/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(21631/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(71817/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(71817/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3051/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3051/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(187/250 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(187/250 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(50893/100000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(50893/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c307059_s2 p hpa hpb X hX hprev1

#print axioms solution
