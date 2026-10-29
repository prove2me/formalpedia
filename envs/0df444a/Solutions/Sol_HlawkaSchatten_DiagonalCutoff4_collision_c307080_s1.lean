-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c307080_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:17:05.681985+00:00
-- url     : https://prove2.me/submissions/fc8d7327-f046-4617-8abd-1824dfcfceab

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
theorem collision_support_c307080_s1_s1_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-1624561351/5000000000 : ℝ)*x 0 + (5823047667/10000000000 : ℝ)*x 1 + (1873669089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1624561351/5000000000 : ℝ)^17 ≤ (11495035199351/50000000000000 : ℝ)^13 := by
    have hnat : (1624561351 : ℕ)^17*50000000000000^13 ≤ 11495035199351^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1624561351 5000000000 11495035199351 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5823047667/10000000000 : ℝ)^17 ≤ (49304767248667/100000000000000 : ℝ)^13 := by
    have hnat : (5823047667 : ℕ)^17*100000000000000^13 ≤ 49304767248667^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5823047667 10000000000 49304767248667 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1873669089/5000000000 : ℝ)^17 ≤ (27705162341971/100000000000000 : ℝ)^13 := by
    have hnat : (1873669089 : ℕ)^17*100000000000000^13 ≤ 27705162341971^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873669089 5000000000 27705162341971 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1624561351/5000000000 : ℝ), (5823047667/10000000000 : ℝ), (1873669089/5000000000 : ℝ)] ![(11495035199351/50000000000000 : ℝ), (49304767248667/100000000000000 : ℝ), (27705162341971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1624561351/5000000000 : ℝ)|^17 ≤ (11495035199351/50000000000000 : ℝ)^13
        have hw : |(-1624561351/5000000000 : ℝ)|=(1624561351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5823047667/10000000000 : ℝ)|^17 ≤ (49304767248667/100000000000000 : ℝ)^13
        have hw : |(5823047667/10000000000 : ℝ)|=(5823047667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1873669089/5000000000 : ℝ)|^17 ≤ (27705162341971/100000000000000 : ℝ)^13
        have hw : |(1873669089/5000000000 : ℝ)|=(1873669089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307080_s1_s1_1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6230434217/10000000000 : ℝ)*x 0 + (41726591/10000000000 : ℝ)*x 1 + (5527608011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6230434217/10000000000 : ℝ)^17 ≤ (420807247933/781250000000 : ℝ)^13 := by
    have hnat : (6230434217 : ℕ)^17*781250000000^13 ≤ 420807247933^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6230434217 10000000000 420807247933 781250000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41726591/10000000000 : ℝ)^17 ≤ (38654696227/50000000000000 : ℝ)^13 := by
    have hnat : (41726591 : ℕ)^17*50000000000000^13 ≤ 38654696227^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41726591 10000000000 38654696227 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5527608011/10000000000 : ℝ)^17 ≤ (46059362858427/100000000000000 : ℝ)^13 := by
    have hnat : (5527608011 : ℕ)^17*100000000000000^13 ≤ 46059362858427^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5527608011 10000000000 46059362858427 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6230434217/10000000000 : ℝ), (41726591/10000000000 : ℝ), (5527608011/10000000000 : ℝ)] ![(420807247933/781250000000 : ℝ), (38654696227/50000000000000 : ℝ), (46059362858427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6230434217/10000000000 : ℝ)|^17 ≤ (420807247933/781250000000 : ℝ)^13
        have hw : |(6230434217/10000000000 : ℝ)|=(6230434217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41726591/10000000000 : ℝ)|^17 ≤ (38654696227/50000000000000 : ℝ)^13
        have hw : |(41726591/10000000000 : ℝ)|=(41726591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5527608011/10000000000 : ℝ)|^17 ≤ (46059362858427/100000000000000 : ℝ)^13
        have hw : |(5527608011/10000000000 : ℝ)|=(5527608011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307080_s1_s1_2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (719013377/2500000000 : ℝ)*x 0 + (6486688329/10000000000 : ℝ)*x 1 + (-414632891/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (719013377/2500000000 : ℝ)^17 ≤ (19600761754703/100000000000000 : ℝ)^13 := by
    have hnat : (719013377 : ℕ)^17*100000000000000^13 ≤ 19600761754703^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      719013377 2500000000 19600761754703 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6486688329/10000000000 : ℝ)^17 ≤ (3548656653429/6250000000000 : ℝ)^13 := by
    have hnat : (6486688329 : ℕ)^17*6250000000000^13 ≤ 3548656653429^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6486688329 10000000000 3548656653429 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (414632891/1250000000 : ℝ)^17 ≤ (1476295736229/6250000000000 : ℝ)^13 := by
    have hnat : (414632891 : ℕ)^17*6250000000000^13 ≤ 1476295736229^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      414632891 1250000000 1476295736229 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(719013377/2500000000 : ℝ), (6486688329/10000000000 : ℝ), (-414632891/1250000000 : ℝ)] ![(19600761754703/100000000000000 : ℝ), (3548656653429/6250000000000 : ℝ), (1476295736229/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(719013377/2500000000 : ℝ)|^17 ≤ (19600761754703/100000000000000 : ℝ)^13
        have hw : |(719013377/2500000000 : ℝ)|=(719013377/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6486688329/10000000000 : ℝ)|^17 ≤ (3548656653429/6250000000000 : ℝ)^13
        have hw : |(6486688329/10000000000 : ℝ)|=(6486688329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-414632891/1250000000 : ℝ)|^17 ≤ (1476295736229/6250000000000 : ℝ)^13
        have hw : |(-414632891/1250000000 : ℝ)|=(414632891/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307080_s1_s1_4 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (0 : ℝ)*x 0 + (1 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (0 : ℝ)^17 ≤ (0 : ℝ)^13 := by
    have hnat : (0 : ℕ)^17*1^13 ≤ 0^13*1^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1 : ℝ)^17 ≤ (1 : ℝ)^13 := by
    have hnat : (1 : ℕ)^17*1^13 ≤ 1^13*1^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^17 ≤ (0 : ℝ)^13 := by
    have hnat : (0 : ℕ)^17*1^13 ≤ 0^13*1^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(0 : ℝ)|^17 ≤ (0 : ℝ)^13
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1 : ℝ)|^17 ≤ (1 : ℝ)^13
        have hw : |(1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^17 ≤ (0 : ℝ)^13
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307080_s1_s1_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-221442451/625000000 : ℝ)*x 0 + (1972772417/5000000000 : ℝ)*x 1 + (168582897/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (221442451/625000000 : ℝ)^17 ≤ (25747129656939/100000000000000 : ℝ)^13 := by
    have hnat : (221442451 : ℕ)^17*100000000000000^13 ≤ 25747129656939^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221442451 625000000 25747129656939 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1972772417/5000000000 : ℝ)^17 ≤ (29636861334559/100000000000000 : ℝ)^13 := by
    have hnat : (1972772417 : ℕ)^17*100000000000000^13 ≤ 29636861334559^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1972772417 5000000000 29636861334559 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168582897/312500000 : ℝ)^17 ≤ (22308004494393/50000000000000 : ℝ)^13 := by
    have hnat : (168582897 : ℕ)^17*50000000000000^13 ≤ 22308004494393^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168582897 312500000 22308004494393 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-221442451/625000000 : ℝ), (1972772417/5000000000 : ℝ), (168582897/312500000 : ℝ)] ![(25747129656939/100000000000000 : ℝ), (29636861334559/100000000000000 : ℝ), (22308004494393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-221442451/625000000 : ℝ)|^17 ≤ (25747129656939/100000000000000 : ℝ)^13
        have hw : |(-221442451/625000000 : ℝ)|=(221442451/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1972772417/5000000000 : ℝ)|^17 ≤ (29636861334559/100000000000000 : ℝ)^13
        have hw : |(1972772417/5000000000 : ℝ)|=(1972772417/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168582897/312500000 : ℝ)|^17 ≤ (22308004494393/50000000000000 : ℝ)^13
        have hw : |(168582897/312500000 : ℝ)|=(168582897/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307080_s1_s1_8 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2513751261/5000000000 : ℝ)*x 0 + (50593703/5000000000 : ℝ)*x 1 + (6685628467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2513751261/5000000000 : ℝ)^17 ≤ (20343735494201/50000000000000 : ℝ)^13 := by
    have hnat : (2513751261 : ℕ)^17*50000000000000^13 ≤ 20343735494201^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2513751261 5000000000 20343735494201 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (50593703/5000000000 : ℝ)^17 ≤ (49243534363/20000000000000 : ℝ)^13 := by
    have hnat : (50593703 : ℕ)^17*20000000000000^13 ≤ 49243534363^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50593703 5000000000 49243534363 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6685628467/10000000000 : ℝ)^17 ≤ (59066311329563/100000000000000 : ℝ)^13 := by
    have hnat : (6685628467 : ℕ)^17*100000000000000^13 ≤ 59066311329563^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6685628467 10000000000 59066311329563 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2513751261/5000000000 : ℝ), (50593703/5000000000 : ℝ), (6685628467/10000000000 : ℝ)] ![(20343735494201/50000000000000 : ℝ), (49243534363/20000000000000 : ℝ), (59066311329563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2513751261/5000000000 : ℝ)|^17 ≤ (20343735494201/50000000000000 : ℝ)^13
        have hw : |(2513751261/5000000000 : ℝ)|=(2513751261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(50593703/5000000000 : ℝ)|^17 ≤ (49243534363/20000000000000 : ℝ)^13
        have hw : |(50593703/5000000000 : ℝ)|=(50593703/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6685628467/10000000000 : ℝ)|^17 ≤ (59066311329563/100000000000000 : ℝ)^13
        have hw : |(6685628467/10000000000 : ℝ)|=(6685628467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307080_s1_s1_9 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1206414611/10000000000 : ℝ)*x 0 + (324984943/400000000 : ℝ)*x 1 + (-263606169/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1206414611/10000000000 : ℝ)^17 ≤ (6293324910321/100000000000000 : ℝ)^13 := by
    have hnat : (1206414611 : ℕ)^17*100000000000000^13 ≤ 6293324910321^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206414611 10000000000 6293324910321 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (324984943/400000000 : ℝ)^17 ≤ (38108372915541/50000000000000 : ℝ)^13 := by
    have hnat : (324984943 : ℕ)^17*50000000000000^13 ≤ 38108372915541^13*400000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      324984943 400000000 38108372915541 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (263606169/1000000000 : ℝ)^17 ≤ (17489929242051/100000000000000 : ℝ)^13 := by
    have hnat : (263606169 : ℕ)^17*100000000000000^13 ≤ 17489929242051^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263606169 1000000000 17489929242051 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1206414611/10000000000 : ℝ), (324984943/400000000 : ℝ), (-263606169/1000000000 : ℝ)] ![(6293324910321/100000000000000 : ℝ), (38108372915541/50000000000000 : ℝ), (17489929242051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1206414611/10000000000 : ℝ)|^17 ≤ (6293324910321/100000000000000 : ℝ)^13
        have hw : |(1206414611/10000000000 : ℝ)|=(1206414611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(324984943/400000000 : ℝ)|^17 ≤ (38108372915541/50000000000000 : ℝ)^13
        have hw : |(324984943/400000000 : ℝ)|=(324984943/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-263606169/1000000000 : ℝ)|^17 ≤ (17489929242051/100000000000000 : ℝ)^13
        have hw : |(-263606169/1000000000 : ℝ)|=(263606169/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307080_s1_s1_13 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2915130831/10000000000 : ℝ)*x 0 + (6412627389/10000000000 : ℝ)*x 1 + (3370330099/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2915130831/10000000000 : ℝ)^17 ≤ (19949749685737/100000000000000 : ℝ)^13 := by
    have hnat : (2915130831 : ℕ)^17*100000000000000^13 ≤ 19949749685737^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2915130831 10000000000 19949749685737 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6412627389/10000000000 : ℝ)^17 ≤ (27966136509143/50000000000000 : ℝ)^13 := by
    have hnat : (6412627389 : ℕ)^17*50000000000000^13 ≤ 27966136509143^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6412627389 10000000000 27966136509143 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3370330099/10000000000 : ℝ)^17 ≤ (24117977276339/100000000000000 : ℝ)^13 := by
    have hnat : (3370330099 : ℕ)^17*100000000000000^13 ≤ 24117977276339^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3370330099 10000000000 24117977276339 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2915130831/10000000000 : ℝ), (6412627389/10000000000 : ℝ), (3370330099/10000000000 : ℝ)] ![(19949749685737/100000000000000 : ℝ), (27966136509143/50000000000000 : ℝ), (24117977276339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2915130831/10000000000 : ℝ)|^17 ≤ (19949749685737/100000000000000 : ℝ)^13
        have hw : |(2915130831/10000000000 : ℝ)|=(2915130831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6412627389/10000000000 : ℝ)|^17 ≤ (27966136509143/50000000000000 : ℝ)^13
        have hw : |(6412627389/10000000000 : ℝ)|=(6412627389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3370330099/10000000000 : ℝ)|^17 ≤ (24117977276339/100000000000000 : ℝ)^13
        have hw : |(3370330099/10000000000 : ℝ)|=(3370330099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307080_s1_s1_14 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-5275042949/10000000000 : ℝ)*x 0 + (2787198163/5000000000 : ℝ)*x 1 + (1732635479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275042949/10000000000 : ℝ)^17 ≤ (43326846139433/100000000000000 : ℝ)^13 := by
    have hnat : (5275042949 : ℕ)^17*100000000000000^13 ≤ 43326846139433^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275042949 10000000000 43326846139433 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2787198163/5000000000 : ℝ)^17 ≤ (9313970690747/20000000000000 : ℝ)^13 := by
    have hnat : (2787198163 : ℕ)^17*20000000000000^13 ≤ 9313970690747^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2787198163 5000000000 9313970690747 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1732635479/10000000000 : ℝ)^17 ≤ (5051650196167/50000000000000 : ℝ)^13 := by
    have hnat : (1732635479 : ℕ)^17*50000000000000^13 ≤ 5051650196167^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1732635479 10000000000 5051650196167 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-5275042949/10000000000 : ℝ), (2787198163/5000000000 : ℝ), (1732635479/10000000000 : ℝ)] ![(43326846139433/100000000000000 : ℝ), (9313970690747/20000000000000 : ℝ), (5051650196167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-5275042949/10000000000 : ℝ)|^17 ≤ (43326846139433/100000000000000 : ℝ)^13
        have hw : |(-5275042949/10000000000 : ℝ)|=(5275042949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2787198163/5000000000 : ℝ)|^17 ≤ (9313970690747/20000000000000 : ℝ)^13
        have hw : |(2787198163/5000000000 : ℝ)|=(2787198163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1732635479/10000000000 : ℝ)|^17 ≤ (5051650196167/50000000000000 : ℝ)^13
        have hw : |(1732635479/10000000000 : ℝ)|=(1732635479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307080_s1_s1_15 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2808370113/5000000000 : ℝ)*x 0 + (6150247/625000000 : ℝ)*x 1 + (1532475357/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2808370113/5000000000 : ℝ)^17 ≤ (11758247700161/25000000000000 : ℝ)^13 := by
    have hnat : (2808370113 : ℕ)^17*25000000000000^13 ≤ 11758247700161^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2808370113 5000000000 11758247700161 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6150247/625000000 : ℝ)^17 ≤ (47479696393/20000000000000 : ℝ)^13 := by
    have hnat : (6150247 : ℕ)^17*20000000000000^13 ≤ 47479696393^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6150247 625000000 47479696393 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1532475357/2500000000 : ℝ)^17 ≤ (10545922141099/20000000000000 : ℝ)^13 := by
    have hnat : (1532475357 : ℕ)^17*20000000000000^13 ≤ 10545922141099^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1532475357 2500000000 10545922141099 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2808370113/5000000000 : ℝ), (6150247/625000000 : ℝ), (1532475357/2500000000 : ℝ)] ![(11758247700161/25000000000000 : ℝ), (47479696393/20000000000000 : ℝ), (10545922141099/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2808370113/5000000000 : ℝ)|^17 ≤ (11758247700161/25000000000000 : ℝ)^13
        have hw : |(2808370113/5000000000 : ℝ)|=(2808370113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6150247/625000000 : ℝ)|^17 ≤ (47479696393/20000000000000 : ℝ)^13
        have hw : |(6150247/625000000 : ℝ)|=(6150247/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1532475357/2500000000 : ℝ)|^17 ≤ (10545922141099/20000000000000 : ℝ)^13
        have hw : |(1532475357/2500000000 : ℝ)|=(1532475357/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307080_s1_s1_16 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (690338411/5000000000 : ℝ)*x 0 + (5719813313/10000000000 : ℝ)*x 1 + (-107359109/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (690338411/5000000000 : ℝ)^17 ≤ (3753833209959/50000000000000 : ℝ)^13 := by
    have hnat : (690338411 : ℕ)^17*50000000000000^13 ≤ 3753833209959^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690338411 5000000000 3753833209959 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5719813313/10000000000 : ℝ)^17 ≤ (24082419731013/50000000000000 : ℝ)^13 := by
    have hnat : (5719813313 : ℕ)^17*50000000000000^13 ≤ 24082419731013^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5719813313 10000000000 24082419731013 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107359109/200000000 : ℝ)^17 ≤ (5540936762347/12500000000000 : ℝ)^13 := by
    have hnat : (107359109 : ℕ)^17*12500000000000^13 ≤ 5540936762347^13*200000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107359109 200000000 5540936762347 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(690338411/5000000000 : ℝ), (5719813313/10000000000 : ℝ), (-107359109/200000000 : ℝ)] ![(3753833209959/50000000000000 : ℝ), (24082419731013/50000000000000 : ℝ), (5540936762347/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(690338411/5000000000 : ℝ)|^17 ≤ (3753833209959/50000000000000 : ℝ)^13
        have hw : |(690338411/5000000000 : ℝ)|=(690338411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5719813313/10000000000 : ℝ)|^17 ≤ (24082419731013/50000000000000 : ℝ)^13
        have hw : |(5719813313/10000000000 : ℝ)|=(5719813313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-107359109/200000000 : ℝ)|^17 ≤ (5540936762347/12500000000000 : ℝ)^13
        have hw : |(-107359109/200000000 : ℝ)|=(107359109/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307080_s1_s1_20 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2808370113/5000000000 : ℝ)*x 0 + (4137096183/10000000000 : ℝ)*x 1 + (3079651069/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2808370113/5000000000 : ℝ)^17 ≤ (11758247700161/25000000000000 : ℝ)^13 := by
    have hnat : (2808370113 : ℕ)^17*25000000000000^13 ≤ 11758247700161^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2808370113 5000000000 11758247700161 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4137096183/10000000000 : ℝ)^17 ≤ (31532311485997/100000000000000 : ℝ)^13 := by
    have hnat : (4137096183 : ℕ)^17*100000000000000^13 ≤ 31532311485997^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4137096183 10000000000 31532311485997 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3079651069/10000000000 : ℝ)^17 ≤ (21434697699533/100000000000000 : ℝ)^13 := by
    have hnat : (3079651069 : ℕ)^17*100000000000000^13 ≤ 21434697699533^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3079651069 10000000000 21434697699533 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2808370113/5000000000 : ℝ), (4137096183/10000000000 : ℝ), (3079651069/10000000000 : ℝ)] ![(11758247700161/25000000000000 : ℝ), (31532311485997/100000000000000 : ℝ), (21434697699533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2808370113/5000000000 : ℝ)|^17 ≤ (11758247700161/25000000000000 : ℝ)^13
        have hw : |(2808370113/5000000000 : ℝ)|=(2808370113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4137096183/10000000000 : ℝ)|^17 ≤ (31532311485997/100000000000000 : ℝ)^13
        have hw : |(4137096183/10000000000 : ℝ)|=(4137096183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3079651069/10000000000 : ℝ)|^17 ≤ (21434697699533/100000000000000 : ℝ)^13
        have hw : |(3079651069/10000000000 : ℝ)|=(3079651069/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307080_s1_s1_21 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-77113911/312500000 : ℝ)*x 0 + (1377600931/2000000000 : ℝ)*x 1 + (3200533173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (77113911/312500000 : ℝ)^17 ≤ (4010816389357/25000000000000 : ℝ)^13 := by
    have hnat : (77113911 : ℕ)^17*25000000000000^13 ≤ 4010816389357^13*312500000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77113911 312500000 4010816389357 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1377600931/2000000000 : ℝ)^17 ≤ (30707611024377/50000000000000 : ℝ)^13 := by
    have hnat : (1377600931 : ℕ)^17*50000000000000^13 ≤ 30707611024377^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377600931 2000000000 30707611024377 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3200533173/10000000000 : ℝ)^17 ≤ (5635378094011/25000000000000 : ℝ)^13 := by
    have hnat : (3200533173 : ℕ)^17*25000000000000^13 ≤ 5635378094011^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3200533173 10000000000 5635378094011 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-77113911/312500000 : ℝ), (1377600931/2000000000 : ℝ), (3200533173/10000000000 : ℝ)] ![(4010816389357/25000000000000 : ℝ), (30707611024377/50000000000000 : ℝ), (5635378094011/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-77113911/312500000 : ℝ)|^17 ≤ (4010816389357/25000000000000 : ℝ)^13
        have hw : |(-77113911/312500000 : ℝ)|=(77113911/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1377600931/2000000000 : ℝ)|^17 ≤ (30707611024377/50000000000000 : ℝ)^13
        have hw : |(1377600931/2000000000 : ℝ)|=(1377600931/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3200533173/10000000000 : ℝ)|^17 ≤ (5635378094011/25000000000000 : ℝ)^13
        have hw : |(3200533173/10000000000 : ℝ)|=(3200533173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307080_s1_s1_22 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (7938725989/10000000000 : ℝ)*x 0 + (1602797/2500000000 : ℝ)*x 1 + (3574800857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7938725989/10000000000 : ℝ)^17 ≤ (73944335118469/100000000000000 : ℝ)^13 := by
    have hnat : (7938725989 : ℕ)^17*100000000000000^13 ≤ 73944335118469^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7938725989 10000000000 73944335118469 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1602797/2500000000 : ℝ)^17 ≤ (1668776069/25000000000000 : ℝ)^13 := by
    have hnat : (1602797 : ℕ)^17*25000000000000^13 ≤ 1668776069^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1602797 2500000000 1668776069 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3574800857/10000000000 : ℝ)^17 ≤ (13024494885019/50000000000000 : ℝ)^13 := by
    have hnat : (3574800857 : ℕ)^17*50000000000000^13 ≤ 13024494885019^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3574800857 10000000000 13024494885019 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7938725989/10000000000 : ℝ), (1602797/2500000000 : ℝ), (3574800857/10000000000 : ℝ)] ![(73944335118469/100000000000000 : ℝ), (1668776069/25000000000000 : ℝ), (13024494885019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7938725989/10000000000 : ℝ)|^17 ≤ (73944335118469/100000000000000 : ℝ)^13
        have hw : |(7938725989/10000000000 : ℝ)|=(7938725989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1602797/2500000000 : ℝ)|^17 ≤ (1668776069/25000000000000 : ℝ)^13
        have hw : |(1602797/2500000000 : ℝ)|=(1602797/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3574800857/10000000000 : ℝ)|^17 ≤ (13024494885019/50000000000000 : ℝ)^13
        have hw : |(3574800857/10000000000 : ℝ)|=(3574800857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307080_s1_s1_23 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (612058471/5000000000 : ℝ)*x 0 + (7978676557/10000000000 : ℝ)*x 1 + (-565164883/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (612058471/5000000000 : ℝ)^17 ≤ (3207177812559/50000000000000 : ℝ)^13 := by
    have hnat : (612058471 : ℕ)^17*50000000000000^13 ≤ 3207177812559^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      612058471 5000000000 3207177812559 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7978676557/10000000000 : ℝ)^17 ≤ (9303915400933/12500000000000 : ℝ)^13 := by
    have hnat : (7978676557 : ℕ)^17*12500000000000^13 ≤ 9303915400933^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7978676557 10000000000 9303915400933 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565164883/2000000000 : ℝ)^17 ≤ (3830864230823/20000000000000 : ℝ)^13 := by
    have hnat : (565164883 : ℕ)^17*20000000000000^13 ≤ 3830864230823^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565164883 2000000000 3830864230823 20000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(612058471/5000000000 : ℝ), (7978676557/10000000000 : ℝ), (-565164883/2000000000 : ℝ)] ![(3207177812559/50000000000000 : ℝ), (9303915400933/12500000000000 : ℝ), (3830864230823/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(612058471/5000000000 : ℝ)|^17 ≤ (3207177812559/50000000000000 : ℝ)^13
        have hw : |(612058471/5000000000 : ℝ)|=(612058471/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(7978676557/10000000000 : ℝ)|^17 ≤ (9303915400933/12500000000000 : ℝ)^13
        have hw : |(7978676557/10000000000 : ℝ)|=(7978676557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-565164883/2000000000 : ℝ)|^17 ≤ (3830864230823/20000000000000 : ℝ)^13
        have hw : |(-565164883/2000000000 : ℝ)|=(565164883/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307080_s1_s1_27 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1697983937/2500000000 : ℝ)*x 0 + (3279494209/10000000000 : ℝ)*x 1 + (2513122871/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1697983937/2500000000 : ℝ)^17 ≤ (30148748340869/50000000000000 : ℝ)^13 := by
    have hnat : (1697983937 : ℕ)^17*50000000000000^13 ≤ 30148748340869^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1697983937 2500000000 30148748340869 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3279494209/10000000000 : ℝ)^17 ≤ (23271499410853/100000000000000 : ℝ)^13 := by
    have hnat : (3279494209 : ℕ)^17*100000000000000^13 ≤ 23271499410853^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3279494209 10000000000 23271499410853 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2513122871/10000000000 : ℝ)^17 ≤ (8215501949363/50000000000000 : ℝ)^13 := by
    have hnat : (2513122871 : ℕ)^17*50000000000000^13 ≤ 8215501949363^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2513122871 10000000000 8215501949363 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1697983937/2500000000 : ℝ), (3279494209/10000000000 : ℝ), (2513122871/10000000000 : ℝ)] ![(30148748340869/50000000000000 : ℝ), (23271499410853/100000000000000 : ℝ), (8215501949363/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1697983937/2500000000 : ℝ)|^17 ≤ (30148748340869/50000000000000 : ℝ)^13
        have hw : |(1697983937/2500000000 : ℝ)|=(1697983937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3279494209/10000000000 : ℝ)|^17 ≤ (23271499410853/100000000000000 : ℝ)^13
        have hw : |(3279494209/10000000000 : ℝ)|=(3279494209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2513122871/10000000000 : ℝ)|^17 ≤ (8215501949363/50000000000000 : ℝ)^13
        have hw : |(2513122871/10000000000 : ℝ)|=(2513122871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c307080_s1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((869/1000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(869/1000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1954/3125 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(1954/3125 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46759/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(46759/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6839/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6839/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((31519/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(31519/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19189/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19189/25000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((-1 : ℝ)*(X 0 2+X 2 2)) ∧ ((-1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((-1 : ℝ)*pair X 1 2) ∧ ((-1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (4817/6250 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base3 : ((1 : ℝ)*N 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 1]
  have base7 : ((1 : ℝ)*T) ≤ (92559/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base8 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 0).1]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 2 0) ≤ (0 : ℝ) := by
    linarith only [order1.1]
  have base53 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2,f.sum]
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
  have s1_pow0 : (869/1000 : ℝ) ^ (135/32 : ℝ) ≤ (55301852800428726841/100000000000000000000 : ℝ) := by
    have hpowers : (869/1000 : ℝ)^135 ≤ (55301852800428726841/100000000000000000000 : ℝ)^32 := by
      have hnat : (869 : ℕ)^135*100000000000000000000^32 ≤ 55301852800428726841^32*1000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        869 1000 55301852800428726841 100000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (869/1000 : ℝ)) (X := (55301852800428726841/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner0a : (155301852800428726841/100000000000000000000 : ℝ) ≤ (5549910095538089/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (155301852800428726841/100000000000000000000 : ℝ)^32 ≤ (5549910095538089/5000000000000000 : ℝ)^135 := by
      have hnat : (155301852800428726841 : ℕ)^32*5000000000000000^135 ≤ 5549910095538089^135*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        155301852800428726841 100000000000000000000 5549910095538089 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5549910095538089/5000000000000000 : ℝ)) (X := (155301852800428726841/100000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner0b : (105301852800428726841/50000000000000000000 : ℝ) ≤ (5965453002280891/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (105301852800428726841/50000000000000000000 : ℝ)^32 ≤ (5965453002280891/5000000000000000 : ℝ)^135 := by
      have hnat : (105301852800428726841 : ℕ)^32*5000000000000000^135 ≤ 5965453002280891^135*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        105301852800428726841 50000000000000000000 5965453002280891 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5965453002280891/5000000000000000 : ℝ)) (X := (105301852800428726841/50000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(49991826867099/395000000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(207771453371401/2172500000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (869/1000 : ℝ)) (alpha := (49991826867099/395000000000000 : ℝ)) (beta := (207771453371401/2172500000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (869/1000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(49991826867099/395000000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(207771453371401/2172500000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (1954/3125 : ℝ) ^ (135/32 : ℝ) ≤ (3448493919834126547/25000000000000000000 : ℝ) := by
    have hpowers : (1954/3125 : ℝ)^135 ≤ (3448493919834126547/25000000000000000000 : ℝ)^32 := by
      have hnat : (1954 : ℕ)^135*25000000000000000000^32 ≤ 3448493919834126547^32*3125^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1954 3125 3448493919834126547 25000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1954/3125 : ℝ)) (X := (3448493919834126547/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner1a : (28448493919834126547/25000000000000000000 : ℝ) ≤ (5155518504849963/5000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (28448493919834126547/25000000000000000000 : ℝ)^32 ≤ (5155518504849963/5000000000000000 : ℝ)^135 := by
      have hnat : (28448493919834126547 : ℕ)^32*5000000000000000^135 ≤ 5155518504849963^135*25000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28448493919834126547 25000000000000000000 5155518504849963 5000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5155518504849963/5000000000000000 : ℝ)) (X := (28448493919834126547/25000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner1b : (15948493919834126547/12500000000000000000 : ℝ) ≤ (264862709779019/250000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (15948493919834126547/12500000000000000000 : ℝ)^32 ≤ (264862709779019/250000000000000 : ℝ)^135 := by
      have hnat : (15948493919834126547 : ℕ)^32*250000000000000^135 ≤ 264862709779019^135*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15948493919834126547 12500000000000000000 264862709779019 250000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (264862709779019/250000000000000 : ℝ)) (X := (15948493919834126547/12500000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(155518504849963/3126400000000000 : ℝ)*((-1 : ℝ)*(X 0 2+X 2 2))+(141735690730417/3126400000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (1954/3125 : ℝ)) (alpha := (155518504849963/3126400000000000 : ℝ)) (beta := (141735690730417/3126400000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 2) ≤ (1954/3125 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(155518504849963/3126400000000000 : ℝ)*((-1 : ℝ)*pair X 1 2)+(141735690730417/3126400000000000 : ℝ)*((-1 : ℝ)*pair X 1 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (46759/50000 : ℝ) ^ (135/32 : ℝ) ≤ (753727166077957421/1000000000000000000 : ℝ) := by
    have hpowers : (46759/50000 : ℝ)^135 ≤ (753727166077957421/1000000000000000000 : ℝ)^32 := by
      have hnat : (46759 : ℕ)^135*1000000000000000000^32 ≤ 753727166077957421^32*50000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        46759 50000 753727166077957421 1000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (46759/50000 : ℝ)) (X := (753727166077957421/1000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner2a : (1753727166077957421/1000000000000000000 : ℝ) ≤ (11424258898867559/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (1753727166077957421/1000000000000000000 : ℝ)^32 ≤ (11424258898867559/10000000000000000 : ℝ)^135 := by
      have hnat : (1753727166077957421 : ℕ)^32*10000000000000000^135 ≤ 11424258898867559^135*1000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1753727166077957421 1000000000000000000 11424258898867559 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11424258898867559/10000000000000000 : ℝ)) (X := (1753727166077957421/1000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s1_corner2b : (1253727166077957421/500000000000000000 : ℝ) ≤ (12434634234619961/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (1253727166077957421/500000000000000000 : ℝ)^32 ≤ (12434634234619961/10000000000000000 : ℝ)^135 := by
      have hnat : (1253727166077957421 : ℕ)^32*10000000000000000^135 ≤ 12434634234619961^135*500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1253727166077957421 500000000000000000 12434634234619961 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12434634234619961/10000000000000000 : ℝ)) (X := (1253727166077957421/500000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(1424258898867559/9351800000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(505187667876201/4675900000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (46759/50000 : ℝ)) (alpha := (1424258898867559/9351800000000000 : ℝ)) (beta := (505187667876201/4675900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (46759/50000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(1424258898867559/9351800000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(505187667876201/4675900000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1624561351/5000000000 : ℝ)*X 0 0+(5823047667/10000000000 : ℝ)*X 0 1+(1873669089/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((6230434217/10000000000 : ℝ)*X 1 0+(41726591/10000000000 : ℝ)*X 1 1+(5527608011/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((719013377/2500000000 : ℝ)*X 2 0+(6486688329/10000000000 : ℝ)*X 2 1+(-414632891/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_4 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s1_s1_4 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-221442451/625000000 : ℝ)*X 0 0+(1972772417/5000000000 : ℝ)*X 0 1+(168582897/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((2513751261/5000000000 : ℝ)*X 1 0+(50593703/5000000000 : ℝ)*X 1 1+(6685628467/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((1206414611/10000000000 : ℝ)*X 2 0+(324984943/400000000 : ℝ)*X 2 1+(-263606169/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((2915130831/10000000000 : ℝ)*X 0 0+(6412627389/10000000000 : ℝ)*X 0 1+(3370330099/10000000000 : ℝ)*X 0 2+(2915130831/10000000000 : ℝ)*X 1 0+(6412627389/10000000000 : ℝ)*X 1 1+(3370330099/10000000000 : ℝ)*X 1 2+(2915130831/10000000000 : ℝ)*X 2 0+(6412627389/10000000000 : ℝ)*X 2 1+(3370330099/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-5275042949/10000000000 : ℝ)*X 0 0+(2787198163/5000000000 : ℝ)*X 0 1+(1732635479/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((2808370113/5000000000 : ℝ)*X 1 0+(6150247/625000000 : ℝ)*X 1 1+(1532475357/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((690338411/5000000000 : ℝ)*X 2 0+(5719813313/10000000000 : ℝ)*X 2 1+(-107359109/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((2808370113/5000000000 : ℝ)*X 0 0+(4137096183/10000000000 : ℝ)*X 0 1+(3079651069/10000000000 : ℝ)*X 0 2+(2808370113/5000000000 : ℝ)*X 1 0+(4137096183/10000000000 : ℝ)*X 1 1+(3079651069/10000000000 : ℝ)*X 1 2+(2808370113/5000000000 : ℝ)*X 2 0+(4137096183/10000000000 : ℝ)*X 2 1+(3079651069/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-77113911/312500000 : ℝ)*X 0 0+(1377600931/2000000000 : ℝ)*X 0 1+(3200533173/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((7938725989/10000000000 : ℝ)*X 1 0+(1602797/2500000000 : ℝ)*X 1 1+(3574800857/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((612058471/5000000000 : ℝ)*X 2 0+(7978676557/10000000000 : ℝ)*X 2 1+(-565164883/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((1697983937/2500000000 : ℝ)*X 0 0+(3279494209/10000000000 : ℝ)*X 0 1+(2513122871/10000000000 : ℝ)*X 0 2+(1697983937/2500000000 : ℝ)*X 1 0+(3279494209/10000000000 : ℝ)*X 1 1+(2513122871/10000000000 : ℝ)*X 1 2+(1697983937/2500000000 : ℝ)*X 2 0+(3279494209/10000000000 : ℝ)*X 2 1+(2513122871/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307080_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((6839/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6839/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (246577730651245493950888732323/17260434290000000000000000000000000 : ℝ) := by norm_num
    linear_combination (212055302397/250000000000 : ℝ)*(base7) + (125470218201/250000000000 : ℝ)*(base49) + (427089/62500000000 : ℝ)*(base53) + (102720041/3906250000 : ℝ)*(base60) + (283761793309/125000000000 : ℝ)*(major_s1_0) + (1135123973843/500000000000 : ℝ)*(major_s1_1) + (2270087513047/1000000000000 : ℝ)*(major_s1_2) + (49515169/1000000000000 : ℝ)*(sp_s1_0) + (76800607/500000000000 : ℝ)*(sp_s1_4) + (255636810533/100000000000 : ℝ)*(sp_s1_7) + (2556417620499/1000000000000 : ℝ)*(sp_s1_8) + (2556276735229/1000000000000 : ℝ)*(sp_s1_9) + (577144326777/250000000000 : ℝ)*(sp_s1_13) + (73859347/500000000000 : ℝ)*(sp_s1_23) + (1460356097519/1000000000000 : ℝ)*(f.failure) + (2556424453923/1000000000000 : ℝ)*(f.sum) + (1285723389123399493/3177985600000000000000000000000 : ℝ)*base63 + (15301140556261/203300000000000000000000000 : ℝ)*base64 + (976355771171889/1563200000000000000000000000 : ℝ)*base66 + (28568959786591/406600000000000000000000000 : ℝ)*base69 + (95968627145268713/401517500000000000000000000000 : ℝ)*base70 + (680451405229489/1086250000000000000000000000 : ℝ)*base72 + (1025898413524669/1563200000000000000000000000 : ℝ)*base75 + (18098296086807/98750000000000000000000000 : ℝ)*base77 + (3434730685456388621/33960520000000000000000000000000 : ℝ)*base78 + (8311/12500000000000000 : ℝ)*base86 + (8311/12500000000000000 : ℝ)*base88 + (4189/12500000000000000 : ℝ)*base91 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((31519/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(31519/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (6743329901421951370015467/4617451250000000000000000000000 : ℝ) := by norm_num
    linear_combination (436328444203/1000000000000 : ℝ)*(base3) + (118883925327/500000000000 : ℝ)*(base7) + (1235891/500000000000 : ℝ)*(base8) + (2727801/1000000000000 : ℝ)*(base24) + (424517389451/500000000000 : ℝ)*(base49) + (883264716121/500000000000 : ℝ)*(major_s1_0) + (883264716121/500000000000 : ℝ)*(major_s1_1) + (883264716121/500000000000 : ℝ)*(major_s1_2) + (403021/500000000000 : ℝ)*(sp_s1_1) + (104351/1000000000000 : ℝ)*(sp_s1_7) + (2249926960441/1000000000000 : ℝ)*(sp_s1_14) + (167891073421/62500000000 : ℝ)*(sp_s1_15) + (1124963404387/500000000000 : ℝ)*(sp_s1_16) + (93785121763/100000000000 : ℝ)*(sp_s1_20) + (1136411811179/1000000000000 : ℝ)*(f.failure) + (89997181463/40000000000 : ℝ)*(f.sum) + (3949700538869230083/14618733760000000000000000000000 : ℝ)*base62 + (832507153928271/2337950000000000000000000000 : ℝ)*base65 + (374134353518317/1563200000000000000000000000 : ℝ)*base67 + (583726386848939/4675900000000000000000000000 : ℝ)*base69 + (1332271665908357011/9234902500000000000000000000000 : ℝ)*base71 + (57068755573021/1086250000000000000000000000 : ℝ)*base73 + (663247125604983/1563200000000000000000000000 : ℝ)*base75 + (26291167400979/197500000000000000000000000 : ℝ)*base77 + (2106390208149318631/33960520000000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (5851/12500000000000000 : ℝ)*base86 + (5851/12500000000000000 : ℝ)*base88 + (5851/12500000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19189/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19189/25000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (266951763370794450575287209807/39698998867000000000000000000000000 : ℝ) := by norm_num
    linear_combination (886879107803/1000000000000 : ℝ)*(base7) + (3972201/1000000000000 : ℝ)*(base11) + (47626557959/200000000000 : ℝ)*(base40) + (136842077063/500000000000 : ℝ)*(base49) + (230066782379/100000000000 : ℝ)*(major_s1_0) + (230066782379/100000000000 : ℝ)*(major_s1_1) + (230066782379/100000000000 : ℝ)*(major_s1_2) + (21293851/1000000000000 : ℝ)*(sp_s1_2) + (193956729/1000000000000 : ℝ)*(sp_s1_9) + (5499/6250000000 : ℝ)*(sp_s1_14) + (643511714253/250000000000 : ℝ)*(sp_s1_21) + (2574051709053/1000000000000 : ℝ)*(sp_s1_22) + (2573836458473/1000000000000 : ℝ)*(sp_s1_23) + (11834515913/5000000000 : ℝ)*(sp_s1_27) + (1480024074797/1000000000000 : ℝ)*(f.failure) + (2574051709053/1000000000000 : ℝ)*(f.sum) + (6199702516207760301/14618733760000000000000000000000 : ℝ)*base62 + (129595228711721/467590000000000000000000000 : ℝ)*base64 + (130830010535481/312640000000000000000000000 : ℝ)*base66 + (84015408316909/187036000000000000000000000 : ℝ)*base68 + (304845047179910289/1846980500000000000000000000000 : ℝ)*base71 + (72843826894123/108625000000000000000000000 : ℝ)*base72 + (34884406042719/62528000000000000000000000 : ℝ)*base74 + (2844616589271/39500000000000000000000000 : ℝ)*base77 + (3322707380989471669/6792104000000000000000000000000 : ℝ)*base78 + (5507/12500000000000000 : ℝ)*base87 + (5507/12500000000000000 : ℝ)*base89 + (5507/12500000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 2, 0], ![2, 0, 1]] ![![true, true, true], ![false, true, false], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((869/1000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(869/1000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1954/3125 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(1954/3125 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(46759/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(46759/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((6839/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6839/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((31519/100000 : ℝ)*X 0 1+(1 : ℝ)*X 0 2+(31519/100000 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(19189/25000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(19189/25000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c307080_s1 p hpa hpb X hX hprev0

#print axioms solution
