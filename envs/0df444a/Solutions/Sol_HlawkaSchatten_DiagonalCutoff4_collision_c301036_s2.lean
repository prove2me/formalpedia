-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c301036_s2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:24:46.877738+00:00
-- url     : https://prove2.me/submissions/6864f6da-4a5d-4393-bb53-db4c5df75fa0

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
theorem collision_support_c301036_s2_s2_0 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1019303867/10000000000 : ℝ)*x 0 + (-1429384757/2500000000 : ℝ)*x 1 + (-5707861387/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1019303867/10000000000 : ℝ)^65 ≤ (4835979627323/100000000000000 : ℝ)^49 := by
    have hnat : (1019303867 : ℕ)^65*100000000000000^49 ≤ 4835979627323^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019303867 10000000000 4835979627323 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1429384757/2500000000 : ℝ)^65 ≤ (4763547376441/10000000000000 : ℝ)^49 := by
    have hnat : (1429384757 : ℕ)^65*10000000000000^49 ≤ 4763547376441^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1429384757 2500000000 4763547376441 10000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5707861387/10000000000 : ℝ)^65 ≤ (5941068324777/12500000000000 : ℝ)^49 := by
    have hnat : (5707861387 : ℕ)^65*12500000000000^49 ≤ 5941068324777^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5707861387 10000000000 5941068324777 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1019303867/10000000000 : ℝ), (-1429384757/2500000000 : ℝ), (-5707861387/10000000000 : ℝ)] ![(4835979627323/100000000000000 : ℝ), (4763547376441/10000000000000 : ℝ), (5941068324777/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1019303867/10000000000 : ℝ)|^65 ≤ (4835979627323/100000000000000 : ℝ)^49
        have hw : |(-1019303867/10000000000 : ℝ)|=(1019303867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1429384757/2500000000 : ℝ)|^65 ≤ (4763547376441/10000000000000 : ℝ)^49
        have hw : |(-1429384757/2500000000 : ℝ)|=(1429384757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5707861387/10000000000 : ℝ)|^65 ≤ (5941068324777/12500000000000 : ℝ)^49
        have hw : |(-5707861387/10000000000 : ℝ)|=(5707861387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301036_s2_s2_1 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1131962007/2000000000 : ℝ)*x 0 + (3671480321/10000000000 : ℝ)*x 1 + (-3677976827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1131962007/2000000000 : ℝ)^65 ≤ (9399702075659/20000000000000 : ℝ)^49 := by
    have hnat : (1131962007 : ℕ)^65*20000000000000^49 ≤ 9399702075659^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131962007 2000000000 9399702075659 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3671480321/10000000000 : ℝ)^65 ≤ (13234835303747/50000000000000 : ℝ)^49 := by
    have hnat : (3671480321 : ℕ)^65*50000000000000^49 ≤ 13234835303747^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3671480321 10000000000 13234835303747 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3677976827/10000000000 : ℝ)^65 ≤ (5306363798517/20000000000000 : ℝ)^49 := by
    have hnat : (3677976827 : ℕ)^65*20000000000000^49 ≤ 5306363798517^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3677976827 10000000000 5306363798517 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1131962007/2000000000 : ℝ), (3671480321/10000000000 : ℝ), (-3677976827/10000000000 : ℝ)] ![(9399702075659/20000000000000 : ℝ), (13234835303747/50000000000000 : ℝ), (5306363798517/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1131962007/2000000000 : ℝ)|^65 ≤ (9399702075659/20000000000000 : ℝ)^49
        have hw : |(1131962007/2000000000 : ℝ)|=(1131962007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3671480321/10000000000 : ℝ)|^65 ≤ (13234835303747/50000000000000 : ℝ)^49
        have hw : |(3671480321/10000000000 : ℝ)|=(3671480321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3677976827/10000000000 : ℝ)|^65 ≤ (5306363798517/20000000000000 : ℝ)^49
        have hw : |(-3677976827/10000000000 : ℝ)|=(3677976827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301036_s2_s2_2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5649148919/10000000000 : ℝ)*x 0 + (-3677609271/10000000000 : ℝ)*x 1 + (1842058311/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5649148919/10000000000 : ℝ)^65 ≤ (23440555128471/50000000000000 : ℝ)^49 := by
    have hnat : (5649148919 : ℕ)^65*50000000000000^49 ≤ 23440555128471^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5649148919 10000000000 23440555128471 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3677609271/10000000000 : ℝ)^65 ≤ (3316037729459/12500000000000 : ℝ)^49 := by
    have hnat : (3677609271 : ℕ)^65*12500000000000^49 ≤ 3316037729459^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3677609271 10000000000 3316037729459 12500000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1842058311/5000000000 : ℝ)^65 ≤ (1063623515309/4000000000000 : ℝ)^49 := by
    have hnat : (1842058311 : ℕ)^65*4000000000000^49 ≤ 1063623515309^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1842058311 5000000000 1063623515309 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5649148919/10000000000 : ℝ), (-3677609271/10000000000 : ℝ), (1842058311/5000000000 : ℝ)] ![(23440555128471/50000000000000 : ℝ), (3316037729459/12500000000000 : ℝ), (1063623515309/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5649148919/10000000000 : ℝ)|^65 ≤ (23440555128471/50000000000000 : ℝ)^49
        have hw : |(5649148919/10000000000 : ℝ)|=(5649148919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3677609271/10000000000 : ℝ)|^65 ≤ (3316037729459/12500000000000 : ℝ)^49
        have hw : |(-3677609271/10000000000 : ℝ)|=(3677609271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1842058311/5000000000 : ℝ)|^65 ≤ (1063623515309/4000000000000 : ℝ)^49
        have hw : |(1842058311/5000000000 : ℝ)|=(1842058311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301036_s2_s2_7 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-97786743/1000000000 : ℝ)*x 0 + (-6019452021/10000000000 : ℝ)*x 1 + (-542433277/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (97786743/1000000000 : ℝ)^65 ≤ (2288471402267/50000000000000 : ℝ)^49 := by
    have hnat : (97786743 : ℕ)^65*50000000000000^49 ≤ 2288471402267^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97786743 1000000000 2288471402267 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6019452021/10000000000 : ℝ)^65 ≤ (1020012634237/2000000000000 : ℝ)^49 := by
    have hnat : (6019452021 : ℕ)^65*2000000000000^49 ≤ 1020012634237^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6019452021 10000000000 1020012634237 2000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542433277/1000000000 : ℝ)^65 ≤ (44422425465467/100000000000000 : ℝ)^49 := by
    have hnat : (542433277 : ℕ)^65*100000000000000^49 ≤ 44422425465467^49*1000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542433277 1000000000 44422425465467 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-97786743/1000000000 : ℝ), (-6019452021/10000000000 : ℝ), (-542433277/1000000000 : ℝ)] ![(2288471402267/50000000000000 : ℝ), (1020012634237/2000000000000 : ℝ), (44422425465467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-97786743/1000000000 : ℝ)|^65 ≤ (2288471402267/50000000000000 : ℝ)^49
        have hw : |(-97786743/1000000000 : ℝ)|=(97786743/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-6019452021/10000000000 : ℝ)|^65 ≤ (1020012634237/2000000000000 : ℝ)^49
        have hw : |(-6019452021/10000000000 : ℝ)|=(6019452021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-542433277/1000000000 : ℝ)|^65 ≤ (44422425465467/100000000000000 : ℝ)^49
        have hw : |(-542433277/1000000000 : ℝ)|=(542433277/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301036_s2_s2_8 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5400375039/10000000000 : ℝ)*x 0 + (4012893681/10000000000 : ℝ)*x 1 + (-725591539/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5400375039/10000000000 : ℝ)^65 ≤ (44162346450739/100000000000000 : ℝ)^49 := by
    have hnat : (5400375039 : ℕ)^65*100000000000000^49 ≤ 44162346450739^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400375039 10000000000 44162346450739 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4012893681/10000000000 : ℝ)^65 ≤ (29783411255513/100000000000000 : ℝ)^49 := by
    have hnat : (4012893681 : ℕ)^65*100000000000000^49 ≤ 29783411255513^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4012893681 10000000000 29783411255513 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (725591539/2000000000 : ℝ)^65 ≤ (26054242281623/100000000000000 : ℝ)^49 := by
    have hnat : (725591539 : ℕ)^65*100000000000000^49 ≤ 26054242281623^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      725591539 2000000000 26054242281623 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5400375039/10000000000 : ℝ), (4012893681/10000000000 : ℝ), (-725591539/2000000000 : ℝ)] ![(44162346450739/100000000000000 : ℝ), (29783411255513/100000000000000 : ℝ), (26054242281623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5400375039/10000000000 : ℝ)|^65 ≤ (44162346450739/100000000000000 : ℝ)^49
        have hw : |(5400375039/10000000000 : ℝ)|=(5400375039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4012893681/10000000000 : ℝ)|^65 ≤ (29783411255513/100000000000000 : ℝ)^49
        have hw : |(4012893681/10000000000 : ℝ)|=(4012893681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-725591539/2000000000 : ℝ)|^65 ≤ (26054242281623/100000000000000 : ℝ)^49
        have hw : |(-725591539/2000000000 : ℝ)|=(725591539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301036_s2_s2_9 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2869352617/5000000000 : ℝ)*x 0 + (-162464757/500000000 : ℝ)*x 1 + (3996342421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2869352617/5000000000 : ℝ)^65 ≤ (373980802591/781250000000 : ℝ)^49 := by
    have hnat : (2869352617 : ℕ)^65*781250000000^49 ≤ 373980802591^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2869352617 5000000000 373980802591 781250000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (162464757/500000000 : ℝ)^65 ≤ (22509890211683/100000000000000 : ℝ)^49 := by
    have hnat : (162464757 : ℕ)^65*100000000000000^49 ≤ 22509890211683^49*500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162464757 500000000 22509890211683 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3996342421/10000000000 : ℝ)^65 ≤ (29620567052703/100000000000000 : ℝ)^49 := by
    have hnat : (3996342421 : ℕ)^65*100000000000000^49 ≤ 29620567052703^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3996342421 10000000000 29620567052703 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2869352617/5000000000 : ℝ), (-162464757/500000000 : ℝ), (3996342421/10000000000 : ℝ)] ![(373980802591/781250000000 : ℝ), (22509890211683/100000000000000 : ℝ), (29620567052703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2869352617/5000000000 : ℝ)|^65 ≤ (373980802591/781250000000 : ℝ)^49
        have hw : |(2869352617/5000000000 : ℝ)|=(2869352617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-162464757/500000000 : ℝ)|^65 ≤ (22509890211683/100000000000000 : ℝ)^49
        have hw : |(-162464757/500000000 : ℝ)|=(162464757/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3996342421/10000000000 : ℝ)|^65 ≤ (29620567052703/100000000000000 : ℝ)^49
        have hw : |(3996342421/10000000000 : ℝ)|=(3996342421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301036_s2_s2_13 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2716798613/5000000000 : ℝ)*x 0 + (-111655377/312500000 : ℝ)*x 1 + (-125916047/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2716798613/5000000000 : ℝ)^65 ≤ (44523098736851/100000000000000 : ℝ)^49 := by
    have hnat : (2716798613 : ℕ)^65*100000000000000^49 ≤ 44523098736851^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716798613 5000000000 44523098736851 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (111655377/312500000 : ℝ)^65 ≤ (1595732632167/6250000000000 : ℝ)^49 := by
    have hnat : (111655377 : ℕ)^65*6250000000000^49 ≤ 1595732632167^49*312500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111655377 312500000 1595732632167 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (125916047/312500000 : ℝ)^65 ≤ (29945179136837/100000000000000 : ℝ)^49 := by
    have hnat : (125916047 : ℕ)^65*100000000000000^49 ≤ 29945179136837^49*312500000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      125916047 312500000 29945179136837 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2716798613/5000000000 : ℝ), (-111655377/312500000 : ℝ), (-125916047/312500000 : ℝ)] ![(44523098736851/100000000000000 : ℝ), (1595732632167/6250000000000 : ℝ), (29945179136837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2716798613/5000000000 : ℝ)|^65 ≤ (44523098736851/100000000000000 : ℝ)^49
        have hw : |(2716798613/5000000000 : ℝ)|=(2716798613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-111655377/312500000 : ℝ)|^65 ≤ (1595732632167/6250000000000 : ℝ)^49
        have hw : |(-111655377/312500000 : ℝ)|=(111655377/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-125916047/312500000 : ℝ)|^65 ≤ (29945179136837/100000000000000 : ℝ)^49
        have hw : |(-125916047/312500000 : ℝ)|=(125916047/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301036_s2_s2_14 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-59804731/2000000000 : ℝ)*x 0 + (-5672757703/10000000000 : ℝ)*x 1 + (-1525007963/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (59804731/2000000000 : ℝ)^65 ≤ (950553891559/100000000000000 : ℝ)^49 := by
    have hnat : (59804731 : ℕ)^65*100000000000000^49 ≤ 950553891559^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59804731 2000000000 950553891559 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5672757703/10000000000 : ℝ)^65 ≤ (47141187113371/100000000000000 : ℝ)^49 := by
    have hnat : (5672757703 : ℕ)^65*100000000000000^49 ≤ 47141187113371^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5672757703 10000000000 47141187113371 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1525007963/2500000000 : ℝ)^65 ≤ (10381651797587/20000000000000 : ℝ)^49 := by
    have hnat : (1525007963 : ℕ)^65*20000000000000^49 ≤ 10381651797587^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1525007963 2500000000 10381651797587 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-59804731/2000000000 : ℝ), (-5672757703/10000000000 : ℝ), (-1525007963/2500000000 : ℝ)] ![(950553891559/100000000000000 : ℝ), (47141187113371/100000000000000 : ℝ), (10381651797587/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-59804731/2000000000 : ℝ)|^65 ≤ (950553891559/100000000000000 : ℝ)^49
        have hw : |(-59804731/2000000000 : ℝ)|=(59804731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5672757703/10000000000 : ℝ)|^65 ≤ (47141187113371/100000000000000 : ℝ)^49
        have hw : |(-5672757703/10000000000 : ℝ)|=(5672757703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1525007963/2500000000 : ℝ)|^65 ≤ (10381651797587/20000000000000 : ℝ)^49
        have hw : |(-1525007963/2500000000 : ℝ)|=(1525007963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301036_s2_s2_15 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2686306353/5000000000 : ℝ)*x 0 + (1895847457/5000000000 : ℝ)*x 1 + (-3883178267/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2686306353/5000000000 : ℝ)^65 ≤ (21930718312469/50000000000000 : ℝ)^49 := by
    have hnat : (2686306353 : ℕ)^65*50000000000000^49 ≤ 21930718312469^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2686306353 5000000000 21930718312469 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1895847457/5000000000 : ℝ)^65 ≤ (5525092959011/20000000000000 : ℝ)^49 := by
    have hnat : (1895847457 : ℕ)^65*20000000000000^49 ≤ 5525092959011^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1895847457 5000000000 5525092959011 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3883178267/10000000000 : ℝ)^65 ≤ (1140523942151/4000000000000 : ℝ)^49 := by
    have hnat : (3883178267 : ℕ)^65*4000000000000^49 ≤ 1140523942151^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3883178267 10000000000 1140523942151 4000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2686306353/5000000000 : ℝ), (1895847457/5000000000 : ℝ), (-3883178267/10000000000 : ℝ)] ![(21930718312469/50000000000000 : ℝ), (5525092959011/20000000000000 : ℝ), (1140523942151/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2686306353/5000000000 : ℝ)|^65 ≤ (21930718312469/50000000000000 : ℝ)^49
        have hw : |(2686306353/5000000000 : ℝ)|=(2686306353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1895847457/5000000000 : ℝ)|^65 ≤ (5525092959011/20000000000000 : ℝ)^49
        have hw : |(1895847457/5000000000 : ℝ)|=(1895847457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3883178267/10000000000 : ℝ)|^65 ≤ (1140523942151/4000000000000 : ℝ)^49
        have hw : |(-3883178267/10000000000 : ℝ)|=(3883178267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301036_s2_s2_16 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6502717949/10000000000 : ℝ)*x 0 + (-1564164467/5000000000 : ℝ)*x 1 + (1601903529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6502717949/10000000000 : ℝ)^65 ≤ (11300422514213/20000000000000 : ℝ)^49 := by
    have hnat : (6502717949 : ℕ)^65*20000000000000^49 ≤ 11300422514213^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6502717949 10000000000 11300422514213 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1564164467/5000000000 : ℝ)^65 ≤ (4281012144859/20000000000000 : ℝ)^49 := by
    have hnat : (1564164467 : ℕ)^65*20000000000000^49 ≤ 4281012144859^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1564164467 5000000000 4281012144859 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1601903529/5000000000 : ℝ)^65 ≤ (35348522701/160000000000 : ℝ)^49 := by
    have hnat : (1601903529 : ℕ)^65*160000000000^49 ≤ 35348522701^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1601903529 5000000000 35348522701 160000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6502717949/10000000000 : ℝ), (-1564164467/5000000000 : ℝ), (1601903529/5000000000 : ℝ)] ![(11300422514213/20000000000000 : ℝ), (4281012144859/20000000000000 : ℝ), (35348522701/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6502717949/10000000000 : ℝ)|^65 ≤ (11300422514213/20000000000000 : ℝ)^49
        have hw : |(6502717949/10000000000 : ℝ)|=(6502717949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1564164467/5000000000 : ℝ)|^65 ≤ (4281012144859/20000000000000 : ℝ)^49
        have hw : |(-1564164467/5000000000 : ℝ)|=(1564164467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1601903529/5000000000 : ℝ)|^65 ≤ (35348522701/160000000000 : ℝ)^49
        have hw : |(1601903529/5000000000 : ℝ)|=(1601903529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301036_s2_s2_19 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2870785301/5000000000 : ℝ)*x 0 + (-3495042749/10000000000 : ℝ)*x 1 + (-1202653/3200000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2870785301/5000000000 : ℝ)^65 ≤ (47901251432007/100000000000000 : ℝ)^49 := by
    have hnat : (2870785301 : ℕ)^65*100000000000000^49 ≤ 47901251432007^49*5000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2870785301 5000000000 47901251432007 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3495042749/10000000000 : ℝ)^65 ≤ (24795664693121/100000000000000 : ℝ)^49 := by
    have hnat : (3495042749 : ℕ)^65*100000000000000^49 ≤ 24795664693121^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3495042749 10000000000 24795664693121 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1202653/3200000 : ℝ)^65 ≤ (13651541926379/50000000000000 : ℝ)^49 := by
    have hnat : (1202653 : ℕ)^65*50000000000000^49 ≤ 13651541926379^49*3200000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1202653 3200000 13651541926379 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2870785301/5000000000 : ℝ), (-3495042749/10000000000 : ℝ), (-1202653/3200000 : ℝ)] ![(47901251432007/100000000000000 : ℝ), (24795664693121/100000000000000 : ℝ), (13651541926379/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2870785301/5000000000 : ℝ)|^65 ≤ (47901251432007/100000000000000 : ℝ)^49
        have hw : |(2870785301/5000000000 : ℝ)|=(2870785301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3495042749/10000000000 : ℝ)|^65 ≤ (24795664693121/100000000000000 : ℝ)^49
        have hw : |(-3495042749/10000000000 : ℝ)|=(3495042749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1202653/3200000 : ℝ)|^65 ≤ (13651541926379/50000000000000 : ℝ)^49
        have hw : |(-1202653/3200000 : ℝ)|=(1202653/3200000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301036_s2_s2_20 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-59931987/2000000000 : ℝ)*x 0 + (-1221667503/2000000000 : ℝ)*x 1 + (-1132801033/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (59931987/2000000000 : ℝ)^65 ≤ (953237922547/100000000000000 : ℝ)^49 := by
    have hnat : (59931987 : ℕ)^65*100000000000000^49 ≤ 953237922547^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      59931987 2000000000 953237922547 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1221667503/2000000000 : ℝ)^65 ≤ (52002035147961/100000000000000 : ℝ)^49 := by
    have hnat : (1221667503 : ℕ)^65*100000000000000^49 ≤ 52002035147961^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1221667503 2000000000 52002035147961 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1132801033/2000000000 : ℝ)^65 ≤ (2940295432749/6250000000000 : ℝ)^49 := by
    have hnat : (1132801033 : ℕ)^65*6250000000000^49 ≤ 2940295432749^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132801033 2000000000 2940295432749 6250000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-59931987/2000000000 : ℝ), (-1221667503/2000000000 : ℝ), (-1132801033/2000000000 : ℝ)] ![(953237922547/100000000000000 : ℝ), (52002035147961/100000000000000 : ℝ), (2940295432749/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-59931987/2000000000 : ℝ)|^65 ≤ (953237922547/100000000000000 : ℝ)^49
        have hw : |(-59931987/2000000000 : ℝ)|=(59931987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1221667503/2000000000 : ℝ)|^65 ≤ (52002035147961/100000000000000 : ℝ)^49
        have hw : |(-1221667503/2000000000 : ℝ)|=(1221667503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1132801033/2000000000 : ℝ)|^65 ≤ (2940295432749/6250000000000 : ℝ)^49
        have hw : |(-1132801033/2000000000 : ℝ)|=(1132801033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301036_s2_s2_21 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (81429467/125000000 : ℝ)*x 0 + (3191673847/10000000000 : ℝ)*x 1 + (-3125763981/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (81429467/125000000 : ℝ)^65 ≤ (14159077554069/25000000000000 : ℝ)^49 := by
    have hnat : (81429467 : ℕ)^65*25000000000000^49 ≤ 14159077554069^49*125000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81429467 125000000 14159077554069 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3191673847/10000000000 : ℝ)^65 ≤ (10990953438677/50000000000000 : ℝ)^49 := by
    have hnat : (3191673847 : ℕ)^65*50000000000000^49 ≤ 10990953438677^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3191673847 10000000000 10990953438677 50000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3125763981/10000000000 : ℝ)^65 ≤ (21381782889037/100000000000000 : ℝ)^49 := by
    have hnat : (3125763981 : ℕ)^65*100000000000000^49 ≤ 21381782889037^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3125763981 10000000000 21381782889037 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(81429467/125000000 : ℝ), (3191673847/10000000000 : ℝ), (-3125763981/10000000000 : ℝ)] ![(14159077554069/25000000000000 : ℝ), (10990953438677/50000000000000 : ℝ), (21381782889037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(81429467/125000000 : ℝ)|^65 ≤ (14159077554069/25000000000000 : ℝ)^49
        have hw : |(81429467/125000000 : ℝ)|=(81429467/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3191673847/10000000000 : ℝ)|^65 ≤ (10990953438677/50000000000000 : ℝ)^49
        have hw : |(3191673847/10000000000 : ℝ)|=(3191673847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3125763981/10000000000 : ℝ)|^65 ≤ (21381782889037/100000000000000 : ℝ)^49
        have hw : |(-3125763981/10000000000 : ℝ)|=(3125763981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301036_s2_s2_22 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (5358891491/10000000000 : ℝ)*x 0 + (-971306253/2500000000 : ℝ)*x 1 + (3804992923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5358891491/10000000000 : ℝ)^65 ≤ (43712902604781/100000000000000 : ℝ)^49 := by
    have hnat : (5358891491 : ℕ)^65*100000000000000^49 ≤ 43712902604781^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5358891491 10000000000 43712902604781 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (971306253/2500000000 : ℝ)^65 ≤ (28533036272657/100000000000000 : ℝ)^49 := by
    have hnat : (971306253 : ℕ)^65*100000000000000^49 ≤ 28533036272657^49*2500000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      971306253 2500000000 28533036272657 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3804992923/10000000000 : ℝ)^65 ≤ (5550812221483/20000000000000 : ℝ)^49 := by
    have hnat : (3804992923 : ℕ)^65*20000000000000^49 ≤ 5550812221483^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3804992923 10000000000 5550812221483 20000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5358891491/10000000000 : ℝ), (-971306253/2500000000 : ℝ), (3804992923/10000000000 : ℝ)] ![(43712902604781/100000000000000 : ℝ), (28533036272657/100000000000000 : ℝ), (5550812221483/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5358891491/10000000000 : ℝ)|^65 ≤ (43712902604781/100000000000000 : ℝ)^49
        have hw : |(5358891491/10000000000 : ℝ)|=(5358891491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-971306253/2500000000 : ℝ)|^65 ≤ (28533036272657/100000000000000 : ℝ)^49
        have hw : |(-971306253/2500000000 : ℝ)|=(971306253/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3804992923/10000000000 : ℝ)|^65 ≤ (5550812221483/20000000000000 : ℝ)^49
        have hw : |(3804992923/10000000000 : ℝ)|=(3804992923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c301036_s2_s2_25 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1148880301/2000000000 : ℝ)*x 0 + (-752355669/2000000000 : ℝ)*x 1 + (-3488139273/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1148880301/2000000000 : ℝ)^65 ≤ (11983145952733/25000000000000 : ℝ)^49 := by
    have hnat : (1148880301 : ℕ)^65*25000000000000^49 ≤ 11983145952733^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1148880301 2000000000 11983145952733 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (752355669/2000000000 : ℝ)^65 ≤ (27336699851011/100000000000000 : ℝ)^49 := by
    have hnat : (752355669 : ℕ)^65*100000000000000^49 ≤ 27336699851011^49*2000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      752355669 2000000000 27336699851011 100000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3488139273/10000000000 : ℝ)^65 ≤ (6182679082109/25000000000000 : ℝ)^49 := by
    have hnat : (3488139273 : ℕ)^65*25000000000000^49 ≤ 6182679082109^49*10000000000^65 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3488139273 10000000000 6182679082109 25000000000000 65 49 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (65/16 : ℝ)) 65 49 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1148880301/2000000000 : ℝ), (-752355669/2000000000 : ℝ), (-3488139273/10000000000 : ℝ)] ![(11983145952733/25000000000000 : ℝ), (27336699851011/100000000000000 : ℝ), (6182679082109/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1148880301/2000000000 : ℝ)|^65 ≤ (11983145952733/25000000000000 : ℝ)^49
        have hw : |(1148880301/2000000000 : ℝ)|=(1148880301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-752355669/2000000000 : ℝ)|^65 ≤ (27336699851011/100000000000000 : ℝ)^49
        have hw : |(-752355669/2000000000 : ℝ)|=(752355669/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3488139273/10000000000 : ℝ)|^65 ≤ (6182679082109/25000000000000 : ℝ)^49
        have hw : |(-3488139273/10000000000 : ℝ)|=(3488139273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c301036_s2 (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((11219/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11219/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-67509/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-67509/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8517/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-8517/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((873/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(873/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-26963/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-26963/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3379/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-3379/12500 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (4759/6250 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (4759/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (4759/6250 : ℝ)*P 1 ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4759/6250 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
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
  have s2_pow0 : (11219/50000 : ℝ) ^ (129/32 : ℝ) ≤ (60477640337003299/25000000000000000000 : ℝ) := by
    have hpowers : (11219/50000 : ℝ)^129 ≤ (60477640337003299/25000000000000000000 : ℝ)^32 := by
      have hnat : (11219 : ℕ)^129*25000000000000000000^32 ≤ 60477640337003299^32*50000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11219 50000 60477640337003299 25000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11219/50000 : ℝ)) (X := (60477640337003299/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner0a : (25060477640337003299/25000000000000000000 : ℝ) ≤ (10005995431984997/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (25060477640337003299/25000000000000000000 : ℝ)^32 ≤ (10005995431984997/10000000000000000 : ℝ)^129 := by
      have hnat : (25060477640337003299 : ℕ)^32*10000000000000000^129 ≤ 10005995431984997^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25060477640337003299 25000000000000000000 10005995431984997 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005995431984997/10000000000000000 : ℝ)) (X := (25060477640337003299/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner0b : (12560477640337003299/12500000000000000000 : ℝ) ≤ (5005989997172063/5000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (12560477640337003299/12500000000000000000 : ℝ)^32 ≤ (5005989997172063/5000000000000000 : ℝ)^129 := by
      have hnat : (12560477640337003299 : ℕ)^32*5000000000000000^129 ≤ 5005989997172063^129*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12560477640337003299 12500000000000000000 5005989997172063 5000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5005989997172063/5000000000000000 : ℝ)) (X := (12560477640337003299/12500000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s2_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(461187075769/172600000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(5984562359129/2243800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (11219/50000 : ℝ)) (alpha := (461187075769/172600000000000 : ℝ)) (beta := (5984562359129/2243800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow0,s2_corner0a]) (by linarith only [s2_pow0,s2_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (11219/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(461187075769/172600000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(5984562359129/2243800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow1 : (67509/100000 : ℝ) ^ (129/32 : ℝ) ≤ (20517018589580302509/100000000000000000000 : ℝ) := by
    have hpowers : (67509/100000 : ℝ)^129 ≤ (20517018589580302509/100000000000000000000 : ℝ)^32 := by
      have hnat : (67509 : ℕ)^129*100000000000000000000^32 ≤ 20517018589580302509^32*100000^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        67509 100000 20517018589580302509 100000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (67509/100000 : ℝ)) (X := (20517018589580302509/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner1a : (120517018589580302509/100000000000000000000 : ℝ) ≤ (654613626944257/625000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (120517018589580302509/100000000000000000000 : ℝ)^32 ≤ (654613626944257/625000000000000 : ℝ)^129 := by
      have hnat : (120517018589580302509 : ℕ)^32*625000000000000^129 ≤ 654613626944257^129*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        120517018589580302509 100000000000000000000 654613626944257 625000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (654613626944257/625000000000000 : ℝ)) (X := (120517018589580302509/100000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner1b : (70517018589580302509/50000000000000000000 : ℝ) ≤ (435613758722589/400000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (70517018589580302509/50000000000000000000 : ℝ)^32 ≤ (435613758722589/400000000000000 : ℝ)^129 := by
      have hnat : (70517018589580302509 : ℕ)^32*400000000000000^129 ≤ 435613758722589^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70517018589580302509 50000000000000000000 435613758722589 400000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (435613758722589/400000000000000 : ℝ)) (X := (70517018589580302509/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s2_1 : P 1 ≤ ((-1 : ℝ)*(X 0 1+X 2 1))+(9871208981419/140643750000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(416525936956613/6750900000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (67509/100000 : ℝ)) (alpha := (9871208981419/140643750000000 : ℝ)) (beta := (416525936956613/6750900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow1,s2_corner1a]) (by linarith only [s2_pow1,s2_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (67509/100000 : ℝ)*((-1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_1])
    change lpNorm p (pair X 1) ≤ ((-1 : ℝ)*pair X 1 1)+(9871208981419/140643750000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(416525936956613/6750900000000000 : ℝ)*((-1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s2_pow2 : (8517/12500 : ℝ) ^ (129/32 : ℝ) ≤ (10648037233948089003/50000000000000000000 : ℝ) := by
    have hpowers : (8517/12500 : ℝ)^129 ≤ (10648037233948089003/50000000000000000000 : ℝ)^32 := by
      have hnat : (8517 : ℕ)^129*50000000000000000000^32 ≤ 10648037233948089003^32*12500^129 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8517 12500 10648037233948089003 50000000000000000000 129 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8517/12500 : ℝ)) (X := (10648037233948089003/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner2a : (60648037233948089003/50000000000000000000 : ℝ) ≤ (10490572579173563/10000000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (60648037233948089003/50000000000000000000 : ℝ)^32 ≤ (10490572579173563/10000000000000000 : ℝ)^129 := by
      have hnat : (60648037233948089003 : ℕ)^32*10000000000000000^129 ≤ 10490572579173563^129*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        60648037233948089003 50000000000000000000 10490572579173563 10000000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10490572579173563/10000000000000000 : ℝ)) (X := (60648037233948089003/50000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have s2_corner2b : (35648037233948089003/25000000000000000000 : ℝ) ≤ (2730016533924213/2500000000000000 : ℝ) ^ (129/32 : ℝ) := by
    have hpowers : (35648037233948089003/25000000000000000000 : ℝ)^32 ≤ (2730016533924213/2500000000000000 : ℝ)^129 := by
      have hnat : (35648037233948089003 : ℕ)^32*2500000000000000^129 ≤ 2730016533924213^129*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        35648037233948089003 25000000000000000000 2730016533924213 2500000000000000 32 129 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2730016533924213/2500000000000000 : ℝ)) (X := (35648037233948089003/25000000000000000000 : ℝ)) (by norm_num) 129 32 (by norm_num) hpowers
    exact h
  have major_s2_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(490572579173563/6813600000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(429493556523289/6813600000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (129/32 : ℝ)) (rho := (8517/12500 : ℝ)) (alpha := (490572579173563/6813600000000000 : ℝ)) (beta := (429493556523289/6813600000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s2_pow2,s2_corner2a]) (by linarith only [s2_pow2,s2_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (8517/12500 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s1_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(490572579173563/6813600000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(429493556523289/6813600000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s2_0 : ((-1019303867/10000000000 : ℝ)*X 0 0+(-1429384757/2500000000 : ℝ)*X 0 1+(-5707861387/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301036_s2_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_1 : ((1131962007/2000000000 : ℝ)*X 1 0+(3671480321/10000000000 : ℝ)*X 1 1+(-3677976827/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301036_s2_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_2 : ((5649148919/10000000000 : ℝ)*X 2 0+(-3677609271/10000000000 : ℝ)*X 2 1+(1842058311/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301036_s2_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_7 : ((-97786743/1000000000 : ℝ)*X 0 0+(-6019452021/10000000000 : ℝ)*X 0 1+(-542433277/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301036_s2_s2_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_8 : ((5400375039/10000000000 : ℝ)*X 1 0+(4012893681/10000000000 : ℝ)*X 1 1+(-725591539/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301036_s2_s2_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_9 : ((2869352617/5000000000 : ℝ)*X 2 0+(-162464757/500000000 : ℝ)*X 2 1+(3996342421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301036_s2_s2_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_13 : ((2716798613/5000000000 : ℝ)*X 0 0+(-111655377/312500000 : ℝ)*X 0 1+(-125916047/312500000 : ℝ)*X 0 2+(2716798613/5000000000 : ℝ)*X 1 0+(-111655377/312500000 : ℝ)*X 1 1+(-125916047/312500000 : ℝ)*X 1 2+(2716798613/5000000000 : ℝ)*X 2 0+(-111655377/312500000 : ℝ)*X 2 1+(-125916047/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301036_s2_s2_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_14 : ((-59804731/2000000000 : ℝ)*X 0 0+(-5672757703/10000000000 : ℝ)*X 0 1+(-1525007963/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301036_s2_s2_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_15 : ((2686306353/5000000000 : ℝ)*X 1 0+(1895847457/5000000000 : ℝ)*X 1 1+(-3883178267/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301036_s2_s2_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_16 : ((6502717949/10000000000 : ℝ)*X 2 0+(-1564164467/5000000000 : ℝ)*X 2 1+(1601903529/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301036_s2_s2_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_19 : ((2870785301/5000000000 : ℝ)*X 0 0+(-3495042749/10000000000 : ℝ)*X 0 1+(-1202653/3200000 : ℝ)*X 0 2+(2870785301/5000000000 : ℝ)*X 1 0+(-3495042749/10000000000 : ℝ)*X 1 1+(-1202653/3200000 : ℝ)*X 1 2+(2870785301/5000000000 : ℝ)*X 2 0+(-3495042749/10000000000 : ℝ)*X 2 1+(-1202653/3200000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301036_s2_s2_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_20 : ((-59931987/2000000000 : ℝ)*X 0 0+(-1221667503/2000000000 : ℝ)*X 0 1+(-1132801033/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c301036_s2_s2_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_21 : ((81429467/125000000 : ℝ)*X 1 0+(3191673847/10000000000 : ℝ)*X 1 1+(-3125763981/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c301036_s2_s2_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_22 : ((5358891491/10000000000 : ℝ)*X 2 0+(-971306253/2500000000 : ℝ)*X 2 1+(3804992923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c301036_s2_s2_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s2_25 : ((1148880301/2000000000 : ℝ)*X 0 0+(-752355669/2000000000 : ℝ)*X 0 1+(-3488139273/10000000000 : ℝ)*X 0 2+(1148880301/2000000000 : ℝ)*X 1 0+(-752355669/2000000000 : ℝ)*X 1 1+(-3488139273/10000000000 : ℝ)*X 1 2+(1148880301/2000000000 : ℝ)*X 2 0+(-752355669/2000000000 : ℝ)*X 2 1+(-3488139273/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c301036_s2_s2_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s2_0 : (0 : ℝ) ≤ ((873/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(873/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (29760075335042221379447634149/3675575511400000000000000000000000 : ℝ) := by norm_num
    linear_combination (375643496163/500000000000 : ℝ)*(base39) + (218495261879/1000000000000 : ℝ)*(base50) + (75350710667/1000000000000 : ℝ)*(base60) + (3071391818739/1000000000000 : ℝ)*(major_s2_0) + (3071391818739/1000000000000 : ℝ)*(major_s2_1) + (3071391818739/1000000000000 : ℝ)*(major_s2_2) + (68685939/1000000000000 : ℝ)*(sp_s2_0) + (254146820741/62500000000 : ℝ)*(sp_s2_7) + (406632218263/100000000000 : ℝ)*(sp_s2_8) + (4066321105901/1000000000000 : ℝ)*(sp_s2_9) + (2076330966401/1000000000000 : ℝ)*(sp_s2_13) + (127789539/1000000000000 : ℝ)*(sp_s2_15) + (16077187/500000000000 : ℝ)*(sp_s2_20) + (128866269/1000000000000 : ℝ)*(sp_s2_22) + (2076330966401/1000000000000 : ℝ)*(f.failure) + (4066449972169/1000000000000 : ℝ)*(f.sum) + (13721569819502722783/17036271200000000000000000000000 : ℝ)*base63 + (903846720128183/2271200000000000000000000000 : ℝ)*base65 + (941476124831141/2250300000000000000000000000 : ℝ)*base67 + (932169638841419/2271200000000000000000000000 : ℝ)*base69 + (185783336488204057/392009120000000000000000000000 : ℝ)*base71 + (129768152844209/2243800000000000000000000000 : ℝ)*base72 + (43855387216819/375050000000000000000000000 : ℝ)*base74 + (68056840967611/172600000000000000000000000 : ℝ)*base77 + (6266008416101147/3884017800000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base85 + (381/25000000000000000 : ℝ)*base87 + (381/25000000000000000 : ℝ)*base89 + (381/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s2_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-26963/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-26963/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (20186875000509907977556131/1663156340000000000000000000000 : ℝ) := by norm_num
    linear_combination (1475074297249/500000000000 : ℝ)*(base39) + (1669306158543/1000000000000 : ℝ)*(base40) + (76762295183/500000000000 : ℝ)*(base60) + (279489665299/50000000000 : ℝ)*(major_s2_0) + (279489665299/50000000000 : ℝ)*(major_s2_1) + (279489665299/50000000000 : ℝ)*(major_s2_2) + (247224241/1000000000000 : ℝ)*(sp_s2_0) + (412157379/1000000000000 : ℝ)*(sp_s2_1) + (28545281/200000000000 : ℝ)*(sp_s2_9) + (44892687/100000000000 : ℝ)*(sp_s2_13) + (7400507493747/1000000000000 : ℝ)*(sp_s2_14) + (231260705019/31250000000 : ℝ)*(sp_s2_15) + (7400611991583/1000000000000 : ℝ)*(sp_s2_16) + (9445947303/2500000000 : ℝ)*(sp_s2_19) + (3778827848071/1000000000000 : ℝ)*(f.failure) + (7400754717987/1000000000000 : ℝ)*(f.sum) + (160182651086287/770872000000000000000000000 : ℝ)*base63 + (1966027255607/20040000000000000000000000 : ℝ)*base64 + (598852051933/10386000000000000000000000 : ℝ)*base67 + (8746763422829/20040000000000000000000000 : ℝ)*base69 + (2115787706531363/17294520000000000000000000000 : ℝ)*base71 + (1601933342573/4315000000000000000000000 : ℝ)*base72 + (399735953717/17310000000000000000000000 : ℝ)*base75 + (2522426181757/8630000000000000000000000 : ℝ)*base77 + (4413749307097811/11203897500000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base85 + (13651/25000000000000000 : ℝ)*base87 + (13651/25000000000000000 : ℝ)*base89 + (13651/25000000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base92 + hcertificate_margin
  have ratio_s2_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3379/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-3379/12500 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (19620558997355908995219647/2548059280000000000000000000000 : ℝ) := by norm_num
    linear_combination (1476276392751/500000000000 : ℝ)*(base39) + (127854966717/100000000000 : ℝ)*(base40) + (154649493263/1000000000000 : ℝ)*(base50) + (694121/250000000000 : ℝ)*(base60) + (1118449237471/200000000000 : ℝ)*(major_s2_0) + (1118449237471/200000000000 : ℝ)*(major_s2_1) + (1118449237471/200000000000 : ℝ)*(major_s2_2) + (147973743/1000000000000 : ℝ)*(sp_s2_2) + (135992819/1000000000000 : ℝ)*(sp_s2_7) + (5811079/62500000000 : ℝ)*(sp_s2_8) + (3701933881647/500000000000 : ℝ)*(sp_s2_20) + (231372211839/31250000000 : ℝ)*(sp_s2_21) + (7403855782369/1000000000000 : ℝ)*(sp_s2_22) + (3780486051861/1000000000000 : ℝ)*(sp_s2_25) + (3780486051861/1000000000000 : ℝ)*(f.failure) + (462750234757/62500000000 : ℝ)*(f.sum) + (1716587079808046053/3407254240000000000000000000000 : ℝ)*base62 + (302549352448231/1362720000000000000000000000 : ℝ)*base64 + (107946315534751/1350180000000000000000000000 : ℝ)*base67 + (153072350060459/1362720000000000000000000000 : ℝ)*base68 + (5198273209770503/235205472000000000000000000000 : ℝ)*base71 + (89186982450489/89752000000000000000000000 : ℝ)*base72 + (53273525767889/225030000000000000000000000 : ℝ)*base75 + (1665937159551/34520000000000000000000000 : ℝ)*base77 + (1633415457275480651/2330410680000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (3359/25000000000000000 : ℝ)*base86 + (3359/25000000000000000 : ℝ)*base88 + (3359/25000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (129/32 : ℝ) ≤ p) (hpb : p ≤ (65/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (36981/25000 : ℝ) (92391/50000 : ℝ) (4759/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, false, false], ![true, false, false]])
    (hprev1 : (0 : ℝ) ≤ ((11219/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(11219/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-67509/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-67509/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-8517/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-8517/12500 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((873/20000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(873/20000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-26963/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(-26963/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-3379/12500 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-3379/12500 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c301036_s2 p hpa hpb X hX hprev1

#print axioms solution
