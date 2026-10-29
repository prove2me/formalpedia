-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c307061_s5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:15:39.057563+00:00
-- url     : https://prove2.me/submissions/6a07d9a0-4456-4ed2-a1fd-80e33e891482

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
theorem collision_support_c307061_s5_s5_0 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-2475137893/10000000000 : ℝ)*x 0 + (227301921/500000000 : ℝ)*x 1 + (5725196393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2475137893/10000000000 : ℝ)^17 ≤ (8053498888209/50000000000000 : ℝ)^13 := by
    have hnat : (2475137893 : ℕ)^17*50000000000000^13 ≤ 8053498888209^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2475137893 10000000000 8053498888209 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (227301921/500000000 : ℝ)^17 ≤ (17834438687047/50000000000000 : ℝ)^13 := by
    have hnat : (227301921 : ℕ)^17*50000000000000^13 ≤ 17834438687047^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227301921 500000000 17834438687047 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5725196393/10000000000 : ℝ)^17 ≤ (48224124831237/100000000000000 : ℝ)^13 := by
    have hnat : (5725196393 : ℕ)^17*100000000000000^13 ≤ 48224124831237^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5725196393 10000000000 48224124831237 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2475137893/10000000000 : ℝ), (227301921/500000000 : ℝ), (5725196393/10000000000 : ℝ)] ![(8053498888209/50000000000000 : ℝ), (17834438687047/50000000000000 : ℝ), (48224124831237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2475137893/10000000000 : ℝ)|^17 ≤ (8053498888209/50000000000000 : ℝ)^13
        have hw : |(-2475137893/10000000000 : ℝ)|=(2475137893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(227301921/500000000 : ℝ)|^17 ≤ (17834438687047/50000000000000 : ℝ)^13
        have hw : |(227301921/500000000 : ℝ)|=(227301921/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5725196393/10000000000 : ℝ)|^17 ≤ (48224124831237/100000000000000 : ℝ)^13
        have hw : |(5725196393/10000000000 : ℝ)|=(5725196393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307061_s5_s5_1 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4711466903/10000000000 : ℝ)*x 0 + (-508892017/2000000000 : ℝ)*x 1 + (1378815989/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4711466903/10000000000 : ℝ)^17 ≤ (37375654330517/100000000000000 : ℝ)^13 := by
    have hnat : (4711466903 : ℕ)^17*100000000000000^13 ≤ 37375654330517^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4711466903 10000000000 37375654330517 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (508892017/2000000000 : ℝ)^17 ≤ (16699443317313/100000000000000 : ℝ)^13 := by
    have hnat : (508892017 : ℕ)^17*100000000000000^13 ≤ 16699443317313^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508892017 2000000000 16699443317313 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1378815989/2500000000 : ℝ)^17 ≤ (45924902335723/100000000000000 : ℝ)^13 := by
    have hnat : (1378815989 : ℕ)^17*100000000000000^13 ≤ 45924902335723^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378815989 2500000000 45924902335723 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4711466903/10000000000 : ℝ), (-508892017/2000000000 : ℝ), (1378815989/2500000000 : ℝ)] ![(37375654330517/100000000000000 : ℝ), (16699443317313/100000000000000 : ℝ), (45924902335723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4711466903/10000000000 : ℝ)|^17 ≤ (37375654330517/100000000000000 : ℝ)^13
        have hw : |(4711466903/10000000000 : ℝ)|=(4711466903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-508892017/2000000000 : ℝ)|^17 ≤ (16699443317313/100000000000000 : ℝ)^13
        have hw : |(-508892017/2000000000 : ℝ)|=(508892017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1378815989/2500000000 : ℝ)|^17 ≤ (45924902335723/100000000000000 : ℝ)^13
        have hw : |(1378815989/2500000000 : ℝ)|=(1378815989/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307061_s5_s5_2 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (237738783/500000000 : ℝ)*x 0 + (3054449159/5000000000 : ℝ)*x 1 + (-1676972111/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (237738783/500000000 : ℝ)^17 ≤ (18912782551123/50000000000000 : ℝ)^13 := by
    have hnat : (237738783 : ℕ)^17*50000000000000^13 ≤ 18912782551123^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      237738783 500000000 18912782551123 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3054449159/5000000000 : ℝ)^17 ≤ (52493475316117/100000000000000 : ℝ)^13 := by
    have hnat : (3054449159 : ℕ)^17*100000000000000^13 ≤ 52493475316117^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3054449159 5000000000 52493475316117 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1676972111/10000000000 : ℝ)^17 ≤ (302529986477/3125000000000 : ℝ)^13 := by
    have hnat : (1676972111 : ℕ)^17*3125000000000^13 ≤ 302529986477^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1676972111 10000000000 302529986477 3125000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(237738783/500000000 : ℝ), (3054449159/5000000000 : ℝ), (-1676972111/10000000000 : ℝ)] ![(18912782551123/50000000000000 : ℝ), (52493475316117/100000000000000 : ℝ), (302529986477/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(237738783/500000000 : ℝ)|^17 ≤ (18912782551123/50000000000000 : ℝ)^13
        have hw : |(237738783/500000000 : ℝ)|=(237738783/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3054449159/5000000000 : ℝ)|^17 ≤ (52493475316117/100000000000000 : ℝ)^13
        have hw : |(3054449159/5000000000 : ℝ)|=(3054449159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1676972111/10000000000 : ℝ)|^17 ≤ (302529986477/3125000000000 : ℝ)^13
        have hw : |(-1676972111/10000000000 : ℝ)|=(1676972111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307061_s5_s5_6 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2922693427/5000000000 : ℝ)*x 0 + (3185920979/10000000000 : ℝ)*x 1 + (3781995521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2922693427/5000000000 : ℝ)^17 ≤ (24776131435507/50000000000000 : ℝ)^13 := by
    have hnat : (2922693427 : ℕ)^17*50000000000000^13 ≤ 24776131435507^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2922693427 5000000000 24776131435507 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3185920979/10000000000 : ℝ)^17 ≤ (5601756658631/25000000000000 : ℝ)^13 := by
    have hnat : (3185920979 : ℕ)^17*25000000000000^13 ≤ 5601756658631^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3185920979 10000000000 5601756658631 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3781995521/10000000000 : ℝ)^17 ≤ (43813610121/156250000000 : ℝ)^13 := by
    have hnat : (3781995521 : ℕ)^17*156250000000^13 ≤ 43813610121^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3781995521 10000000000 43813610121 156250000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2922693427/5000000000 : ℝ), (3185920979/10000000000 : ℝ), (3781995521/10000000000 : ℝ)] ![(24776131435507/50000000000000 : ℝ), (5601756658631/25000000000000 : ℝ), (43813610121/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2922693427/5000000000 : ℝ)|^17 ≤ (24776131435507/50000000000000 : ℝ)^13
        have hw : |(2922693427/5000000000 : ℝ)|=(2922693427/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3185920979/10000000000 : ℝ)|^17 ≤ (5601756658631/25000000000000 : ℝ)^13
        have hw : |(3185920979/10000000000 : ℝ)|=(3185920979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3781995521/10000000000 : ℝ)|^17 ≤ (43813610121/156250000000 : ℝ)^13
        have hw : |(3781995521/10000000000 : ℝ)|=(3781995521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307061_s5_s5_7 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-621552061/2500000000 : ℝ)*x 0 + (4201424141/10000000000 : ℝ)*x 1 + (1206269209/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (621552061/2500000000 : ℝ)^17 ≤ (8100634656437/50000000000000 : ℝ)^13 := by
    have hnat : (621552061 : ℕ)^17*50000000000000^13 ≤ 8100634656437^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      621552061 2500000000 8100634656437 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4201424141/10000000000 : ℝ)^17 ≤ (32174998452529/100000000000000 : ℝ)^13 := by
    have hnat : (4201424141 : ℕ)^17*100000000000000^13 ≤ 32174998452529^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4201424141 10000000000 32174998452529 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1206269209/2000000000 : ℝ)^17 ≤ (25811866111231/50000000000000 : ℝ)^13 := by
    have hnat : (1206269209 : ℕ)^17*50000000000000^13 ≤ 25811866111231^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1206269209 2000000000 25811866111231 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-621552061/2500000000 : ℝ), (4201424141/10000000000 : ℝ), (1206269209/2000000000 : ℝ)] ![(8100634656437/50000000000000 : ℝ), (32174998452529/100000000000000 : ℝ), (25811866111231/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-621552061/2500000000 : ℝ)|^17 ≤ (8100634656437/50000000000000 : ℝ)^13
        have hw : |(-621552061/2500000000 : ℝ)|=(621552061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4201424141/10000000000 : ℝ)|^17 ≤ (32174998452529/100000000000000 : ℝ)^13
        have hw : |(4201424141/10000000000 : ℝ)|=(4201424141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1206269209/2000000000 : ℝ)|^17 ≤ (25811866111231/50000000000000 : ℝ)^13
        have hw : |(1206269209/2000000000 : ℝ)|=(1206269209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307061_s5_s5_8 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2258858041/5000000000 : ℝ)*x 0 + (-272083463/1250000000 : ℝ)*x 1 + (5976066369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2258858041/5000000000 : ℝ)^17 ≤ (35378559385009/100000000000000 : ℝ)^13 := by
    have hnat : (2258858041 : ℕ)^17*100000000000000^13 ≤ 35378559385009^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2258858041 5000000000 35378559385009 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (272083463/1250000000 : ℝ)^17 ≤ (13615571242441/100000000000000 : ℝ)^13 := by
    have hnat : (272083463 : ℕ)^17*100000000000000^13 ≤ 13615571242441^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272083463 1250000000 13615571242441 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5976066369/10000000000 : ℝ)^17 ≤ (25502934678067/50000000000000 : ℝ)^13 := by
    have hnat : (5976066369 : ℕ)^17*50000000000000^13 ≤ 25502934678067^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5976066369 10000000000 25502934678067 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2258858041/5000000000 : ℝ), (-272083463/1250000000 : ℝ), (5976066369/10000000000 : ℝ)] ![(35378559385009/100000000000000 : ℝ), (13615571242441/100000000000000 : ℝ), (25502934678067/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2258858041/5000000000 : ℝ)|^17 ≤ (35378559385009/100000000000000 : ℝ)^13
        have hw : |(2258858041/5000000000 : ℝ)|=(2258858041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-272083463/1250000000 : ℝ)|^17 ≤ (13615571242441/100000000000000 : ℝ)^13
        have hw : |(-272083463/1250000000 : ℝ)|=(272083463/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5976066369/10000000000 : ℝ)|^17 ≤ (25502934678067/50000000000000 : ℝ)^13
        have hw : |(5976066369/10000000000 : ℝ)|=(5976066369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307061_s5_s5_9 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4561129037/10000000000 : ℝ)*x 0 + (820860363/1250000000 : ℝ)*x 1 + (-24667963/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4561129037/10000000000 : ℝ)^17 ≤ (17911895651787/50000000000000 : ℝ)^13 := by
    have hnat : (4561129037 : ℕ)^17*50000000000000^13 ≤ 17911895651787^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4561129037 10000000000 17911895651787 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (820860363/1250000000 : ℝ)^17 ≤ (28849090739047/50000000000000 : ℝ)^13 := by
    have hnat : (820860363 : ℕ)^17*50000000000000^13 ≤ 28849090739047^13*1250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      820860363 1250000000 28849090739047 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (24667963/200000000 : ℝ)^17 ≤ (6478027202349/100000000000000 : ℝ)^13 := by
    have hnat : (24667963 : ℕ)^17*100000000000000^13 ≤ 6478027202349^13*200000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24667963 200000000 6478027202349 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4561129037/10000000000 : ℝ), (820860363/1250000000 : ℝ), (-24667963/200000000 : ℝ)] ![(17911895651787/50000000000000 : ℝ), (28849090739047/50000000000000 : ℝ), (6478027202349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4561129037/10000000000 : ℝ)|^17 ≤ (17911895651787/50000000000000 : ℝ)^13
        have hw : |(4561129037/10000000000 : ℝ)|=(4561129037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(820860363/1250000000 : ℝ)|^17 ≤ (28849090739047/50000000000000 : ℝ)^13
        have hw : |(820860363/1250000000 : ℝ)|=(820860363/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-24667963/200000000 : ℝ)|^17 ≤ (6478027202349/100000000000000 : ℝ)^13
        have hw : |(-24667963/200000000 : ℝ)|=(24667963/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307061_s5_s5_13 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2928116557/5000000000 : ℝ)*x 0 + (3789167021/10000000000 : ℝ)*x 1 + (791315277/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2928116557/5000000000 : ℝ)^17 ≤ (1986901341511/4000000000000 : ℝ)^13 := by
    have hnat : (2928116557 : ℕ)^17*4000000000000^13 ≤ 1986901341511^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2928116557 5000000000 1986901341511 4000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3789167021/10000000000 : ℝ)^17 ≤ (7027565642317/25000000000000 : ℝ)^13 := by
    have hnat : (3789167021 : ℕ)^17*25000000000000^13 ≤ 7027565642317^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3789167021 10000000000 7027565642317 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (791315277/2500000000 : ℝ)^17 ≤ (11108601941743/50000000000000 : ℝ)^13 := by
    have hnat : (791315277 : ℕ)^17*50000000000000^13 ≤ 11108601941743^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      791315277 2500000000 11108601941743 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2928116557/5000000000 : ℝ), (3789167021/10000000000 : ℝ), (791315277/2500000000 : ℝ)] ![(1986901341511/4000000000000 : ℝ), (7027565642317/25000000000000 : ℝ), (11108601941743/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2928116557/5000000000 : ℝ)|^17 ≤ (1986901341511/4000000000000 : ℝ)^13
        have hw : |(2928116557/5000000000 : ℝ)|=(2928116557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3789167021/10000000000 : ℝ)|^17 ≤ (7027565642317/25000000000000 : ℝ)^13
        have hw : |(3789167021/10000000000 : ℝ)|=(3789167021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(791315277/2500000000 : ℝ)|^17 ≤ (11108601941743/50000000000000 : ℝ)^13
        have hw : |(791315277/2500000000 : ℝ)|=(791315277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307061_s5_s5_14 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-951358301/5000000000 : ℝ)*x 0 + (116711553/250000000 : ℝ)*x 1 + (6033732679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (951358301/5000000000 : ℝ)^17 ≤ (713712135241/6250000000000 : ℝ)^13 := by
    have hnat : (951358301 : ℕ)^17*6250000000000^13 ≤ 713712135241^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      951358301 5000000000 713712135241 6250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (116711553/250000000 : ℝ)^17 ≤ (18465079371151/50000000000000 : ℝ)^13 := by
    have hnat : (116711553 : ℕ)^17*50000000000000^13 ≤ 18465079371151^13*250000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116711553 250000000 18465079371151 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6033732679/10000000000 : ℝ)^17 ≤ (6456305885909/12500000000000 : ℝ)^13 := by
    have hnat : (6033732679 : ℕ)^17*12500000000000^13 ≤ 6456305885909^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6033732679 10000000000 6456305885909 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-951358301/5000000000 : ℝ), (116711553/250000000 : ℝ), (6033732679/10000000000 : ℝ)] ![(713712135241/6250000000000 : ℝ), (18465079371151/50000000000000 : ℝ), (6456305885909/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-951358301/5000000000 : ℝ)|^17 ≤ (713712135241/6250000000000 : ℝ)^13
        have hw : |(-951358301/5000000000 : ℝ)|=(951358301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(116711553/250000000 : ℝ)|^17 ≤ (18465079371151/50000000000000 : ℝ)^13
        have hw : |(116711553/250000000 : ℝ)|=(116711553/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6033732679/10000000000 : ℝ)|^17 ≤ (6456305885909/12500000000000 : ℝ)^13
        have hw : |(6033732679/10000000000 : ℝ)|=(6033732679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307061_s5_s5_15 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1094951267/2500000000 : ℝ)*x 0 + (-2343319189/10000000000 : ℝ)*x 1 + (5978452823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1094951267/2500000000 : ℝ)^17 ≤ (16986471723963/50000000000000 : ℝ)^13 := by
    have hnat : (1094951267 : ℕ)^17*50000000000000^13 ≤ 16986471723963^13*2500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094951267 2500000000 16986471723963 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2343319189/10000000000 : ℝ)^17 ≤ (7497274938719/50000000000000 : ℝ)^13 := by
    have hnat : (2343319189 : ℕ)^17*50000000000000^13 ≤ 7497274938719^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2343319189 10000000000 7497274938719 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5978452823/10000000000 : ℝ)^17 ≤ (51032506647239/100000000000000 : ℝ)^13 := by
    have hnat : (5978452823 : ℕ)^17*100000000000000^13 ≤ 51032506647239^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5978452823 10000000000 51032506647239 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1094951267/2500000000 : ℝ), (-2343319189/10000000000 : ℝ), (5978452823/10000000000 : ℝ)] ![(16986471723963/50000000000000 : ℝ), (7497274938719/50000000000000 : ℝ), (51032506647239/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1094951267/2500000000 : ℝ)|^17 ≤ (16986471723963/50000000000000 : ℝ)^13
        have hw : |(1094951267/2500000000 : ℝ)|=(1094951267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2343319189/10000000000 : ℝ)|^17 ≤ (7497274938719/50000000000000 : ℝ)^13
        have hw : |(-2343319189/10000000000 : ℝ)|=(2343319189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5978452823/10000000000 : ℝ)|^17 ≤ (51032506647239/100000000000000 : ℝ)^13
        have hw : |(5978452823/10000000000 : ℝ)|=(5978452823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307061_s5_s5_16 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (534451421/1000000000 : ℝ)*x 0 + (364838007/625000000 : ℝ)*x 1 + (-615505503/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534451421/1000000000 : ℝ)^17 ≤ (22037265182153/50000000000000 : ℝ)^13 := by
    have hnat : (534451421 : ℕ)^17*50000000000000^13 ≤ 22037265182153^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534451421 1000000000 22037265182153 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (364838007/625000000 : ℝ)^17 ≤ (49463833000987/100000000000000 : ℝ)^13 := by
    have hnat : (364838007 : ℕ)^17*100000000000000^13 ≤ 49463833000987^13*625000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      364838007 625000000 49463833000987 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (615505503/5000000000 : ℝ)^17 ≤ (6461636624297/100000000000000 : ℝ)^13 := by
    have hnat : (615505503 : ℕ)^17*100000000000000^13 ≤ 6461636624297^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      615505503 5000000000 6461636624297 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534451421/1000000000 : ℝ), (364838007/625000000 : ℝ), (-615505503/5000000000 : ℝ)] ![(22037265182153/50000000000000 : ℝ), (49463833000987/100000000000000 : ℝ), (6461636624297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534451421/1000000000 : ℝ)|^17 ≤ (22037265182153/50000000000000 : ℝ)^13
        have hw : |(534451421/1000000000 : ℝ)|=(534451421/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(364838007/625000000 : ℝ)|^17 ≤ (49463833000987/100000000000000 : ℝ)^13
        have hw : |(364838007/625000000 : ℝ)|=(364838007/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-615505503/5000000000 : ℝ)|^17 ≤ (6461636624297/100000000000000 : ℝ)^13
        have hw : |(-615505503/5000000000 : ℝ)|=(615505503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307061_s5_s5_20 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6568646331/10000000000 : ℝ)*x 0 + (2933080369/10000000000 : ℝ)*x 1 + (632045669/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6568646331/10000000000 : ℝ)^17 ≤ (57718443549829/100000000000000 : ℝ)^13 := by
    have hnat : (6568646331 : ℕ)^17*100000000000000^13 ≤ 57718443549829^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6568646331 10000000000 57718443549829 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2933080369/10000000000 : ℝ)^17 ≤ (2011053592179/10000000000000 : ℝ)^13 := by
    have hnat : (2933080369 : ℕ)^17*10000000000000^13 ≤ 2011053592179^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2933080369 10000000000 2011053592179 10000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (632045669/2000000000 : ℝ)^17 ≤ (554275512837/2500000000000 : ℝ)^13 := by
    have hnat : (632045669 : ℕ)^17*2500000000000^13 ≤ 554275512837^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      632045669 2000000000 554275512837 2500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6568646331/10000000000 : ℝ), (2933080369/10000000000 : ℝ), (632045669/2000000000 : ℝ)] ![(57718443549829/100000000000000 : ℝ), (2011053592179/10000000000000 : ℝ), (554275512837/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6568646331/10000000000 : ℝ)|^17 ≤ (57718443549829/100000000000000 : ℝ)^13
        have hw : |(6568646331/10000000000 : ℝ)|=(6568646331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2933080369/10000000000 : ℝ)|^17 ≤ (2011053592179/10000000000000 : ℝ)^13
        have hw : |(2933080369/10000000000 : ℝ)|=(2933080369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(632045669/2000000000 : ℝ)|^17 ≤ (554275512837/2500000000000 : ℝ)^13
        have hw : |(632045669/2000000000 : ℝ)|=(632045669/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307061_s5_s5_21 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-952882983/5000000000 : ℝ)*x 0 + (49180367/100000000 : ℝ)*x 1 + (579765411/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (952882983/5000000000 : ℝ)^17 ≤ (5721666163453/50000000000000 : ℝ)^13 := by
    have hnat : (952882983 : ℕ)^17*50000000000000^13 ≤ 5721666163453^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      952882983 5000000000 5721666163453 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49180367/100000000 : ℝ)^17 ≤ (9883220184139/25000000000000 : ℝ)^13 := by
    have hnat : (49180367 : ℕ)^17*25000000000000^13 ≤ 9883220184139^13*100000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49180367 100000000 9883220184139 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (579765411/1000000000 : ℝ)^17 ≤ (24511893460559/50000000000000 : ℝ)^13 := by
    have hnat : (579765411 : ℕ)^17*50000000000000^13 ≤ 24511893460559^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      579765411 1000000000 24511893460559 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-952882983/5000000000 : ℝ), (49180367/100000000 : ℝ), (579765411/1000000000 : ℝ)] ![(5721666163453/50000000000000 : ℝ), (9883220184139/25000000000000 : ℝ), (24511893460559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-952882983/5000000000 : ℝ)|^17 ≤ (5721666163453/50000000000000 : ℝ)^13
        have hw : |(-952882983/5000000000 : ℝ)|=(952882983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(49180367/100000000 : ℝ)|^17 ≤ (9883220184139/25000000000000 : ℝ)^13
        have hw : |(49180367/100000000 : ℝ)|=(49180367/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(579765411/1000000000 : ℝ)|^17 ≤ (24511893460559/50000000000000 : ℝ)^13
        have hw : |(579765411/1000000000 : ℝ)|=(579765411/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307061_s5_s5_22 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2649027463/5000000000 : ℝ)*x 0 + (-989002799/5000000000 : ℝ)*x 1 + (2687888393/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2649027463/5000000000 : ℝ)^17 ≤ (43574178908743/100000000000000 : ℝ)^13 := by
    have hnat : (2649027463 : ℕ)^17*100000000000000^13 ≤ 43574178908743^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2649027463 5000000000 43574178908743 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (989002799/5000000000 : ℝ)^17 ≤ (3003462026749/25000000000000 : ℝ)^13 := by
    have hnat : (989002799 : ℕ)^17*25000000000000^13 ≤ 3003462026749^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989002799 5000000000 3003462026749 25000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687888393/5000000000 : ℝ)^17 ≤ (22205986484593/50000000000000 : ℝ)^13 := by
    have hnat : (2687888393 : ℕ)^17*50000000000000^13 ≤ 22205986484593^13*5000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687888393 5000000000 22205986484593 50000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2649027463/5000000000 : ℝ), (-989002799/5000000000 : ℝ), (2687888393/5000000000 : ℝ)] ![(43574178908743/100000000000000 : ℝ), (3003462026749/25000000000000 : ℝ), (22205986484593/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2649027463/5000000000 : ℝ)|^17 ≤ (43574178908743/100000000000000 : ℝ)^13
        have hw : |(2649027463/5000000000 : ℝ)|=(2649027463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-989002799/5000000000 : ℝ)|^17 ≤ (3003462026749/25000000000000 : ℝ)^13
        have hw : |(-989002799/5000000000 : ℝ)|=(989002799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687888393/5000000000 : ℝ)|^17 ≤ (22205986484593/50000000000000 : ℝ)^13
        have hw : |(2687888393/5000000000 : ℝ)|=(2687888393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307061_s5_s5_23 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (873169867/2000000000 : ℝ)*x 0 + (325968031/500000000 : ℝ)*x 1 + (-1588124629/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873169867/2000000000 : ℝ)^17 ≤ (33831454176669/100000000000000 : ℝ)^13 := by
    have hnat : (873169867 : ℕ)^17*100000000000000^13 ≤ 33831454176669^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873169867 2000000000 33831454176669 100000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (325968031/500000000 : ℝ)^17 ≤ (7144096742923/12500000000000 : ℝ)^13 := by
    have hnat : (325968031 : ℕ)^17*12500000000000^13 ≤ 7144096742923^13*500000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      325968031 500000000 7144096742923 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1588124629/10000000000 : ℝ)^17 ≤ (180315437193/2000000000000 : ℝ)^13 := by
    have hnat : (1588124629 : ℕ)^17*2000000000000^13 ≤ 180315437193^13*10000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1588124629 10000000000 180315437193 2000000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873169867/2000000000 : ℝ), (325968031/500000000 : ℝ), (-1588124629/10000000000 : ℝ)] ![(33831454176669/100000000000000 : ℝ), (7144096742923/12500000000000 : ℝ), (180315437193/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873169867/2000000000 : ℝ)|^17 ≤ (33831454176669/100000000000000 : ℝ)^13
        have hw : |(873169867/2000000000 : ℝ)|=(873169867/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(325968031/500000000 : ℝ)|^17 ≤ (7144096742923/12500000000000 : ℝ)^13
        have hw : |(325968031/500000000 : ℝ)|=(325968031/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1588124629/10000000000 : ℝ)|^17 ≤ (180315437193/2000000000000 : ℝ)^13
        have hw : |(-1588124629/10000000000 : ℝ)|=(1588124629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c307061_s5_s5_27 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1337927733/2000000000 : ℝ)*x 0 + (279704309/1000000000 : ℝ)*x 1 + (314023211/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337927733/2000000000 : ℝ)^17 ≤ (147781615797/250000000000 : ℝ)^13 := by
    have hnat : (1337927733 : ℕ)^17*250000000000^13 ≤ 147781615797^13*2000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337927733 2000000000 147781615797 250000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (279704309/1000000000 : ℝ)^17 ≤ (2362450712999/12500000000000 : ℝ)^13 := by
    have hnat : (279704309 : ℕ)^17*12500000000000^13 ≤ 2362450712999^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      279704309 1000000000 2362450712999 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (314023211/1000000000 : ℝ)^17 ≤ (2748468495111/12500000000000 : ℝ)^13 := by
    have hnat : (314023211 : ℕ)^17*12500000000000^13 ≤ 2748468495111^13*1000000000^17 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      314023211 1000000000 2748468495111 12500000000000 17 13 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (17/4 : ℝ)) 17 13 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337927733/2000000000 : ℝ), (279704309/1000000000 : ℝ), (314023211/1000000000 : ℝ)] ![(147781615797/250000000000 : ℝ), (2362450712999/12500000000000 : ℝ), (2748468495111/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337927733/2000000000 : ℝ)|^17 ≤ (147781615797/250000000000 : ℝ)^13
        have hw : |(1337927733/2000000000 : ℝ)|=(1337927733/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(279704309/1000000000 : ℝ)|^17 ≤ (2362450712999/12500000000000 : ℝ)^13
        have hw : |(279704309/1000000000 : ℝ)|=(279704309/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(314023211/1000000000 : ℝ)|^17 ≤ (2748468495111/12500000000000 : ℝ)^13
        have hw : |(314023211/1000000000 : ℝ)|=(314023211/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c307061_s5 (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev4 : (0 : ℝ) ≤ ((10567/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10567/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48487/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(48487/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44079/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(44079/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((22599/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22599/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27229/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(27229/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(25171/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(25171/100000 : ℝ)*X 1 2) := by
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
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev4 with ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩
  have s5_pow0 : (10567/25000 : ℝ) ^ (135/32 : ℝ) ≤ (21150802069053299/800000000000000000 : ℝ) := by
    have hpowers : (10567/25000 : ℝ)^135 ≤ (21150802069053299/800000000000000000 : ℝ)^32 := by
      have hnat : (10567 : ℕ)^135*800000000000000000^32 ≤ 21150802069053299^32*25000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10567 25000 21150802069053299 800000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10567/25000 : ℝ)) (X := (21150802069053299/800000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s5_corner0a : (821150802069053299/800000000000000000 : ℝ) ≤ (10062046620184023/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (821150802069053299/800000000000000000 : ℝ)^32 ≤ (10062046620184023/10000000000000000 : ℝ)^135 := by
      have hnat : (821150802069053299 : ℕ)^32*10000000000000000^135 ≤ 10062046620184023^135*800000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        821150802069053299 800000000000000000 10062046620184023 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10062046620184023/10000000000000000 : ℝ)) (X := (821150802069053299/800000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s5_corner0b : (421150802069053299/400000000000000000 : ℝ) ≤ (1012288561891649/1000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (421150802069053299/400000000000000000 : ℝ)^32 ≤ (1012288561891649/1000000000000000 : ℝ)^135 := by
      have hnat : (421150802069053299 : ℕ)^32*1000000000000000^135 ≤ 1012288561891649^135*400000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        421150802069053299 400000000000000000 1012288561891649 1000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1012288561891649/1000000000000000 : ℝ)) (X := (421150802069053299/400000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s5_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(62046620184023/4226800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(60838998732467/4226800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (10567/25000 : ℝ)) (alpha := (62046620184023/4226800000000000 : ℝ)) (beta := (60838998732467/4226800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow0,s5_corner0a]) (by linarith only [s5_pow0,s5_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (10567/25000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(62046620184023/4226800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(60838998732467/4226800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow1 : (48487/100000 : ℝ) ^ (135/32 : ℝ) ≤ (589714501003906733/12500000000000000000 : ℝ) := by
    have hpowers : (48487/100000 : ℝ)^135 ≤ (589714501003906733/12500000000000000000 : ℝ)^32 := by
      have hnat : (48487 : ℕ)^135*12500000000000000000^32 ≤ 589714501003906733^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48487 100000 589714501003906733 12500000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (48487/100000 : ℝ)) (X := (589714501003906733/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s5_corner1a : (13089714501003906733/12500000000000000000 : ℝ) ≤ (2527467200600897/2500000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (13089714501003906733/12500000000000000000 : ℝ)^32 ≤ (2527467200600897/2500000000000000 : ℝ)^135 := by
      have hnat : (13089714501003906733 : ℕ)^32*2500000000000000^135 ≤ 2527467200600897^135*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13089714501003906733 12500000000000000000 2527467200600897 2500000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2527467200600897/2500000000000000 : ℝ)) (X := (13089714501003906733/12500000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s5_corner1b : (6839714501003906733/6250000000000000000 : ℝ) ≤ (2554005891276537/2500000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (6839714501003906733/6250000000000000000 : ℝ)^32 ≤ (2554005891276537/2500000000000000 : ℝ)^135 := by
      have hnat : (6839714501003906733 : ℕ)^32*2500000000000000^135 ≤ 2554005891276537^135*6250000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6839714501003906733 6250000000000000000 2554005891276537 2500000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2554005891276537/2500000000000000 : ℝ)) (X := (6839714501003906733/6250000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s5_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(27467200600897/1212175000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(663467266891/30304375000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (48487/100000 : ℝ)) (alpha := (27467200600897/1212175000000000 : ℝ)) (beta := (663467266891/30304375000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow1,s5_corner1a]) (by linarith only [s5_pow1,s5_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (48487/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(27467200600897/1212175000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(663467266891/30304375000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s5_pow2 : (44079/100000 : ℝ) ^ (135/32 : ℝ) ≤ (315575024735745363/10000000000000000000 : ℝ) := by
    have hpowers : (44079/100000 : ℝ)^135 ≤ (315575024735745363/10000000000000000000 : ℝ)^32 := by
      have hnat : (44079 : ℕ)^135*10000000000000000000^32 ≤ 315575024735745363^32*100000^135 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        44079 100000 315575024735745363 10000000000000000000 135 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (44079/100000 : ℝ)) (X := (315575024735745363/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s5_corner2a : (10315575024735745363/10000000000000000000 : ℝ) ≤ (10073918790116879/10000000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (10315575024735745363/10000000000000000000 : ℝ)^32 ≤ (10073918790116879/10000000000000000 : ℝ)^135 := by
      have hnat : (10315575024735745363 : ℕ)^32*10000000000000000^135 ≤ 10073918790116879^135*10000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10315575024735745363 10000000000000000000 10073918790116879 10000000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10073918790116879/10000000000000000 : ℝ)) (X := (10315575024735745363/10000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have s5_corner2b : (5315575024735745363/5000000000000000000 : ℝ) ≤ (2536532971165953/2500000000000000 : ℝ) ^ (135/32 : ℝ) := by
    have hpowers : (5315575024735745363/5000000000000000000 : ℝ)^32 ≤ (2536532971165953/2500000000000000 : ℝ)^135 := by
      have hnat : (5315575024735745363 : ℕ)^32*2500000000000000^135 ≤ 2536532971165953^135*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5315575024735745363 5000000000000000000 2536532971165953 2500000000000000 32 135 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2536532971165953/2500000000000000 : ℝ)) (X := (5315575024735745363/5000000000000000000 : ℝ)) (by norm_num) 135 32 (by norm_num) hpowers
    exact h
  have major_s5_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(73918790116879/4407900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(72213094546933/4407900000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (135/32 : ℝ)) (rho := (44079/100000 : ℝ)) (alpha := (73918790116879/4407900000000000 : ℝ)) (beta := (72213094546933/4407900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s5_pow2,s5_corner2a]) (by linarith only [s5_pow2,s5_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (44079/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s4_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(73918790116879/4407900000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(72213094546933/4407900000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s5_0 : ((-2475137893/10000000000 : ℝ)*X 0 0+(227301921/500000000 : ℝ)*X 0 1+(5725196393/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s5_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_1 : ((4711466903/10000000000 : ℝ)*X 1 0+(-508892017/2000000000 : ℝ)*X 1 1+(1378815989/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s5_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_2 : ((237738783/500000000 : ℝ)*X 2 0+(3054449159/5000000000 : ℝ)*X 2 1+(-1676972111/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s5_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_6 : ((2922693427/5000000000 : ℝ)*X 0 0+(3185920979/10000000000 : ℝ)*X 0 1+(3781995521/10000000000 : ℝ)*X 0 2+(2922693427/5000000000 : ℝ)*X 1 0+(3185920979/10000000000 : ℝ)*X 1 1+(3781995521/10000000000 : ℝ)*X 1 2+(2922693427/5000000000 : ℝ)*X 2 0+(3185920979/10000000000 : ℝ)*X 2 1+(3781995521/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s5_s5_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_7 : ((-621552061/2500000000 : ℝ)*X 0 0+(4201424141/10000000000 : ℝ)*X 0 1+(1206269209/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s5_s5_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_8 : ((2258858041/5000000000 : ℝ)*X 1 0+(-272083463/1250000000 : ℝ)*X 1 1+(5976066369/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s5_s5_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_9 : ((4561129037/10000000000 : ℝ)*X 2 0+(820860363/1250000000 : ℝ)*X 2 1+(-24667963/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s5_s5_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_13 : ((2928116557/5000000000 : ℝ)*X 0 0+(3789167021/10000000000 : ℝ)*X 0 1+(791315277/2500000000 : ℝ)*X 0 2+(2928116557/5000000000 : ℝ)*X 1 0+(3789167021/10000000000 : ℝ)*X 1 1+(791315277/2500000000 : ℝ)*X 1 2+(2928116557/5000000000 : ℝ)*X 2 0+(3789167021/10000000000 : ℝ)*X 2 1+(791315277/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s5_s5_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_14 : ((-951358301/5000000000 : ℝ)*X 0 0+(116711553/250000000 : ℝ)*X 0 1+(6033732679/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s5_s5_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_15 : ((1094951267/2500000000 : ℝ)*X 1 0+(-2343319189/10000000000 : ℝ)*X 1 1+(5978452823/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s5_s5_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_16 : ((534451421/1000000000 : ℝ)*X 2 0+(364838007/625000000 : ℝ)*X 2 1+(-615505503/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s5_s5_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_20 : ((6568646331/10000000000 : ℝ)*X 0 0+(2933080369/10000000000 : ℝ)*X 0 1+(632045669/2000000000 : ℝ)*X 0 2+(6568646331/10000000000 : ℝ)*X 1 0+(2933080369/10000000000 : ℝ)*X 1 1+(632045669/2000000000 : ℝ)*X 1 2+(6568646331/10000000000 : ℝ)*X 2 0+(2933080369/10000000000 : ℝ)*X 2 1+(632045669/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s5_s5_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_21 : ((-952882983/5000000000 : ℝ)*X 0 0+(49180367/100000000 : ℝ)*X 0 1+(579765411/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s5_s5_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_22 : ((2649027463/5000000000 : ℝ)*X 1 0+(-989002799/5000000000 : ℝ)*X 1 1+(2687888393/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s5_s5_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_23 : ((873169867/2000000000 : ℝ)*X 2 0+(325968031/500000000 : ℝ)*X 2 1+(-1588124629/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s5_s5_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s5_27 : ((1337927733/2000000000 : ℝ)*X 0 0+(279704309/1000000000 : ℝ)*X 0 1+(314023211/1000000000 : ℝ)*X 0 2+(1337927733/2000000000 : ℝ)*X 1 0+(279704309/1000000000 : ℝ)*X 1 1+(314023211/1000000000 : ℝ)*X 1 2+(1337927733/2000000000 : ℝ)*X 2 0+(279704309/1000000000 : ℝ)*X 2 1+(314023211/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c307061_s5_s5_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s5_0 : (0 : ℝ) ≤ ((22599/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22599/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (8510635810063261991496319648241/752813676139700000000000000000000000 : ℝ) := by norm_num
    linear_combination (549467/250000000000 : ℝ)*(base50) + (707689053951/500000000000 : ℝ)*(base59) + (194233/1000000000000 : ℝ)*(base60) + (8332943037161/1000000000000 : ℝ)*(major_s5_0) + (8332943037161/1000000000000 : ℝ)*(major_s5_1) + (8332943037161/1000000000000 : ℝ)*(major_s5_2) + (59356681/1000000000000 : ℝ)*(sp_s5_0) + (35998607/1000000000000 : ℝ)*(sp_s5_6) + (5652612262949/500000000000 : ℝ)*(sp_s5_7) + (11304982549163/1000000000000 : ℝ)*(sp_s5_8) + (2826292760189/250000000000 : ℝ)*(sp_s5_9) + (1340140606191/250000000000 : ℝ)*(sp_s5_13) + (37666677/125000000000 : ℝ)*(sp_s5_15) + (112841823/1000000000000 : ℝ)*(sp_s5_23) + (5360598423371/1000000000000 : ℝ)*(f.failure) + (11305283882579/1000000000000 : ℝ)*(f.sum) + (14020338129352112671/42745169460000000000000000000000 : ℝ)*base63 + (2750289614805863/4407900000000000000000000000 : ℝ)*base64 + (186006093428679/242435000000000000000000000 : ℝ)*base66 + (1425825598890601/4407900000000000000000000000 : ℝ)*base68 + (65571278114273023667/186313117200000000000000000000000 : ℝ)*base70 + (1638533695608133/4226800000000000000000000000 : ℝ)*base72 + (199484781635851/2424350000000000000000000000 : ℝ)*base74 + (1622256956890377/4226800000000000000000000000 : ℝ)*base76 + (98947583951112722771/204944851600000000000000000000000 : ℝ)*base78 + (9401/12500000000000000 : ℝ)*base87 + (9401/12500000000000000 : ℝ)*base89 + (9401/12500000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s5_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27229/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(27229/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (1521406863461203647008984250999/301125470455880000000000000000000000 : ℝ) := by norm_num
    linear_combination (129989/500000000000 : ℝ)*(base39) + (159687/1000000000000 : ℝ)*(base49) + (510148988389/500000000000 : ℝ)*(base59) + (1600103712537/200000000000 : ℝ)*(major_s5_0) + (1600103712537/200000000000 : ℝ)*(major_s5_1) + (1600103712537/200000000000 : ℝ)*(major_s5_2) + (11177999/500000000000 : ℝ)*(sp_s5_2) + (27149873/1000000000000 : ℝ)*(sp_s5_6) + (8315947/200000000000 : ℝ)*(sp_s5_7) + (10854244747523/1000000000000 : ℝ)*(sp_s5_14) + (5427143163629/500000000000 : ℝ)*(sp_s5_15) + (542713198563/50000000000 : ℝ)*(sp_s5_16) + (5146485998839/1000000000000 : ℝ)*(sp_s5_20) + (235965259/1000000000000 : ℝ)*(sp_s5_27) + (514674911397/100000000000 : ℝ)*(f.failure) + (5427143163629/500000000000 : ℝ)*(f.sum) + (31798536839859997/113987118560000000000000000000 : ℝ)*base62 + (1530569453611/11754400000000000000000000 : ℝ)*base65 + (11338164377897/48487000000000000000000000 : ℝ)*base67 + (94092553876239/293860000000000000000000000 : ℝ)*base68 + (2538795337093978279/12420874480000000000000000000000 : ℝ)*base71 + (569544763365253/845360000000000000000000000 : ℝ)*base72 + (20444521180833/60608750000000000000000000 : ℝ)*base74 + (165510937159521/845360000000000000000000000 : ℝ)*base76 + (5177005754312735747/40988970320000000000000000000000 : ℝ)*base78 + (1143/1250000000000000 : ℝ)*base86 + (1143/1250000000000000 : ℝ)*base88 + (1143/1250000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s5_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(25171/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(25171/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (24678694021955387591128911/1552609310000000000000000000000 : ℝ) := by norm_num
    linear_combination (15030480127/40000000000 : ℝ)*(base40) + (588207/250000000000 : ℝ)*(base50) + (1030972331879/1000000000000 : ℝ)*(base59) + (1888823339667/250000000000 : ℝ)*(major_s5_0) + (1888823339667/250000000000 : ℝ)*(major_s5_1) + (1888823339667/250000000000 : ℝ)*(major_s5_2) + (271453217/500000000000 : ℝ)*(sp_s5_0) + (2223267/4000000000 : ℝ)*(sp_s5_1) + (5860001/500000000000 : ℝ)*(sp_s5_2) + (59344421/500000000000 : ℝ)*(sp_s5_9) + (10249703636169/1000000000000 : ℝ)*(sp_s5_21) + (10249690725853/1000000000000 : ℝ)*(sp_s5_22) + (5125058066879/500000000000 : ℝ)*(sp_s5_23) + (4860334876401/1000000000000 : ℝ)*(sp_s5_27) + (4860334876401/1000000000000 : ℝ)*(f.failure) + (10250246542603/1000000000000 : ℝ)*(f.sum) + (3197804049993221969/7124194910000000000000000000000 : ℝ)*base62 + (832775015161/45915625000000000000000000 : ℝ)*base65 + (142953592002207/242435000000000000000000000 : ℝ)*base67 + (100208460020117/734650000000000000000000000 : ℝ)*base69 + (5441300872209128937/15526093100000000000000000000000 : ℝ)*base71 + (325813207642071/1056700000000000000000000000 : ℝ)*base72 + (434809550702377/2424350000000000000000000000 : ℝ)*base75 + (1323924417158161/1056700000000000000000000000 : ℝ)*base77 + (8297999039829428237/51236212900000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base84 + (2169/12500000000000000 : ℝ)*base86 + (2169/12500000000000000 : ℝ)*base88 + (2169/12500000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s5_0,ratio_s5_1,ratio_s5_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (135/32 : ℝ) ≤ p) (hpb : p ≤ (17/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (19431/12500 : ℝ) (92559/50000 : ℝ) (4817/6250 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev4 : (0 : ℝ) ≤ ((10567/25000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(10567/25000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(48487/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(48487/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(44079/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(44079/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((22599/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(22599/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(27229/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(27229/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(25171/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(25171/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c307061_s5 p hpa hpb X hX hprev4

#print axioms solution
