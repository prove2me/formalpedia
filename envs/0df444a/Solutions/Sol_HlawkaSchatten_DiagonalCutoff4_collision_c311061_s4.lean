-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c311061_s4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:01:21.329049+00:00
-- url     : https://prove2.me/submissions/4e30ce1b-7266-4c6c-bb45-acddadd73307

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
theorem collision_support_c311061_s4_s4_0 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-2478411167/10000000000 : ℝ)*x 0 + (89895061/200000000 : ℝ)*x 1 + (1122670193/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2478411167/10000000000 : ℝ)^9 ≤ (16637192081989/100000000000000 : ℝ)^7 := by
    have hnat : (2478411167 : ℕ)^9*100000000000000^7 ≤ 16637192081989^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2478411167 10000000000 16637192081989 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89895061/200000000 : ℝ)^9 ≤ (357667049193/1000000000000 : ℝ)^7 := by
    have hnat : (89895061 : ℕ)^9*1000000000000^7 ≤ 357667049193^7*200000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89895061 200000000 357667049193 1000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122670193/2000000000 : ℝ)^9 ≤ (9519220598061/20000000000000 : ℝ)^7 := by
    have hnat : (1122670193 : ℕ)^9*20000000000000^7 ≤ 9519220598061^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122670193 2000000000 9519220598061 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2478411167/10000000000 : ℝ), (89895061/200000000 : ℝ), (1122670193/2000000000 : ℝ)] ![(16637192081989/100000000000000 : ℝ), (357667049193/1000000000000 : ℝ), (9519220598061/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2478411167/10000000000 : ℝ)|^9 ≤ (16637192081989/100000000000000 : ℝ)^7
        have hw : |(-2478411167/10000000000 : ℝ)|=(2478411167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(89895061/200000000 : ℝ)|^9 ≤ (357667049193/1000000000000 : ℝ)^7
        have hw : |(89895061/200000000 : ℝ)|=(89895061/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1122670193/2000000000 : ℝ)|^9 ≤ (9519220598061/20000000000000 : ℝ)^7
        have hw : |(1122670193/2000000000 : ℝ)|=(1122670193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s4_s4_1 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4667119309/10000000000 : ℝ)*x 0 + (-2503409381/10000000000 : ℝ)*x 1 + (271501473/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4667119309/10000000000 : ℝ)^9 ≤ (37539756130893/100000000000000 : ℝ)^7 := by
    have hnat : (4667119309 : ℕ)^9*100000000000000^7 ≤ 37539756130893^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4667119309 10000000000 37539756130893 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2503409381/10000000000 : ℝ)^9 ≤ (4213314213061/25000000000000 : ℝ)^7 := by
    have hnat : (2503409381 : ℕ)^9*25000000000000^7 ≤ 4213314213061^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2503409381 10000000000 4213314213061 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271501473/500000000 : ℝ)^9 ≤ (45606986998767/100000000000000 : ℝ)^7 := by
    have hnat : (271501473 : ℕ)^9*100000000000000^7 ≤ 45606986998767^7*500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271501473 500000000 45606986998767 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4667119309/10000000000 : ℝ), (-2503409381/10000000000 : ℝ), (271501473/500000000 : ℝ)] ![(37539756130893/100000000000000 : ℝ), (4213314213061/25000000000000 : ℝ), (45606986998767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4667119309/10000000000 : ℝ)|^9 ≤ (37539756130893/100000000000000 : ℝ)^7
        have hw : |(4667119309/10000000000 : ℝ)|=(4667119309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2503409381/10000000000 : ℝ)|^9 ≤ (4213314213061/25000000000000 : ℝ)^7
        have hw : |(-2503409381/10000000000 : ℝ)|=(2503409381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271501473/500000000 : ℝ)|^9 ≤ (45606986998767/100000000000000 : ℝ)^7
        have hw : |(271501473/500000000 : ℝ)|=(271501473/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s4_s4_2 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2338652771/5000000000 : ℝ)*x 0 + (6012053853/10000000000 : ℝ)*x 1 + (-214470341/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2338652771/5000000000 : ℝ)^9 ≤ (37645130730611/100000000000000 : ℝ)^7 := by
    have hnat : (2338652771 : ℕ)^9*100000000000000^7 ≤ 37645130730611^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2338652771 5000000000 37645130730611 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6012053853/10000000000 : ℝ)^9 ≤ (51986016107847/100000000000000 : ℝ)^7 := by
    have hnat : (6012053853 : ℕ)^9*100000000000000^7 ≤ 51986016107847^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6012053853 10000000000 51986016107847 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (214470341/1250000000 : ℝ)^9 ≤ (2592213285083/25000000000000 : ℝ)^7 := by
    have hnat : (214470341 : ℕ)^9*25000000000000^7 ≤ 2592213285083^7*1250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214470341 1250000000 2592213285083 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2338652771/5000000000 : ℝ), (6012053853/10000000000 : ℝ), (-214470341/1250000000 : ℝ)] ![(37645130730611/100000000000000 : ℝ), (51986016107847/100000000000000 : ℝ), (2592213285083/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2338652771/5000000000 : ℝ)|^9 ≤ (37645130730611/100000000000000 : ℝ)^7
        have hw : |(2338652771/5000000000 : ℝ)|=(2338652771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6012053853/10000000000 : ℝ)|^9 ≤ (51986016107847/100000000000000 : ℝ)^7
        have hw : |(6012053853/10000000000 : ℝ)|=(6012053853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-214470341/1250000000 : ℝ)|^9 ≤ (2592213285083/25000000000000 : ℝ)^7
        have hw : |(-214470341/1250000000 : ℝ)|=(214470341/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s4_s4_6 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2914569373/5000000000 : ℝ)*x 0 + (1556717247/5000000000 : ℝ)*x 1 + (3687674709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2914569373/5000000000 : ℝ)^9 ≤ (49961356229607/100000000000000 : ℝ)^7 := by
    have hnat : (2914569373 : ℕ)^9*100000000000000^7 ≤ 49961356229607^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2914569373 5000000000 49961356229607 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1556717247/5000000000 : ℝ)^9 ≤ (22307509411547/100000000000000 : ℝ)^7 := by
    have hnat : (1556717247 : ℕ)^9*100000000000000^7 ≤ 22307509411547^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1556717247 5000000000 22307509411547 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3687674709/10000000000 : ℝ)^9 ≤ (27731134342127/100000000000000 : ℝ)^7 := by
    have hnat : (3687674709 : ℕ)^9*100000000000000^7 ≤ 27731134342127^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3687674709 10000000000 27731134342127 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2914569373/5000000000 : ℝ), (1556717247/5000000000 : ℝ), (3687674709/10000000000 : ℝ)] ![(49961356229607/100000000000000 : ℝ), (22307509411547/100000000000000 : ℝ), (27731134342127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2914569373/5000000000 : ℝ)|^9 ≤ (49961356229607/100000000000000 : ℝ)^7
        have hw : |(2914569373/5000000000 : ℝ)|=(2914569373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1556717247/5000000000 : ℝ)|^9 ≤ (22307509411547/100000000000000 : ℝ)^7
        have hw : |(1556717247/5000000000 : ℝ)|=(1556717247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3687674709/10000000000 : ℝ)|^9 ≤ (27731134342127/100000000000000 : ℝ)^7
        have hw : |(3687674709/10000000000 : ℝ)|=(3687674709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s4_s4_7 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-1237558853/5000000000 : ℝ)*x 0 + (4496387063/10000000000 : ℝ)*x 1 + (5614424289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1237558853/5000000000 : ℝ)^9 ≤ (16608772270767/100000000000000 : ℝ)^7 := by
    have hnat : (1237558853 : ℕ)^9*100000000000000^7 ≤ 16608772270767^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1237558853 5000000000 16608772270767 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4496387063/10000000000 : ℝ)^9 ≤ (2236463959653/6250000000000 : ℝ)^7 := by
    have hnat : (4496387063 : ℕ)^9*6250000000000^7 ≤ 2236463959653^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4496387063 10000000000 2236463959653 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5614424289/10000000000 : ℝ)^9 ≤ (23803902175561/50000000000000 : ℝ)^7 := by
    have hnat : (5614424289 : ℕ)^9*50000000000000^7 ≤ 23803902175561^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5614424289 10000000000 23803902175561 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1237558853/5000000000 : ℝ), (4496387063/10000000000 : ℝ), (5614424289/10000000000 : ℝ)] ![(16608772270767/100000000000000 : ℝ), (2236463959653/6250000000000 : ℝ), (23803902175561/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1237558853/5000000000 : ℝ)|^9 ≤ (16608772270767/100000000000000 : ℝ)^7
        have hw : |(-1237558853/5000000000 : ℝ)|=(1237558853/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4496387063/10000000000 : ℝ)|^9 ≤ (2236463959653/6250000000000 : ℝ)^7
        have hw : |(4496387063/10000000000 : ℝ)|=(4496387063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5614424289/10000000000 : ℝ)|^9 ≤ (23803902175561/50000000000000 : ℝ)^7
        have hw : |(5614424289/10000000000 : ℝ)|=(5614424289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s4_s4_8 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2317328991/5000000000 : ℝ)*x 0 + (-475754413/2000000000 : ℝ)*x 1 + (5559826929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2317328991/5000000000 : ℝ)^9 ≤ (37204388743141/100000000000000 : ℝ)^7 := by
    have hnat : (2317328991 : ℕ)^9*100000000000000^7 ≤ 37204388743141^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2317328991 5000000000 37204388743141 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (475754413/2000000000 : ℝ)^9 ≤ (7891106927683/50000000000000 : ℝ)^7 := by
    have hnat : (475754413 : ℕ)^9*50000000000000^7 ≤ 7891106927683^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      475754413 2000000000 7891106927683 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5559826929/10000000000 : ℝ)^9 ≤ (1880535895729/4000000000000 : ℝ)^7 := by
    have hnat : (5559826929 : ℕ)^9*4000000000000^7 ≤ 1880535895729^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5559826929 10000000000 1880535895729 4000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2317328991/5000000000 : ℝ), (-475754413/2000000000 : ℝ), (5559826929/10000000000 : ℝ)] ![(37204388743141/100000000000000 : ℝ), (7891106927683/50000000000000 : ℝ), (1880535895729/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2317328991/5000000000 : ℝ)|^9 ≤ (37204388743141/100000000000000 : ℝ)^7
        have hw : |(2317328991/5000000000 : ℝ)|=(2317328991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-475754413/2000000000 : ℝ)|^9 ≤ (7891106927683/50000000000000 : ℝ)^7
        have hw : |(-475754413/2000000000 : ℝ)|=(475754413/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5559826929/10000000000 : ℝ)|^9 ≤ (1880535895729/4000000000000 : ℝ)^7
        have hw : |(5559826929/10000000000 : ℝ)|=(5559826929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s4_s4_9 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (464484489/1000000000 : ℝ)*x 0 + (153280919/250000000 : ℝ)*x 1 + (-1586522441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (464484489/1000000000 : ℝ)^9 ≤ (37309560616857/100000000000000 : ℝ)^7 := by
    have hnat : (464484489 : ℕ)^9*100000000000000^7 ≤ 37309560616857^7*1000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464484489 1000000000 37309560616857 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (153280919/250000000 : ℝ)^9 ≤ (53314770035991/100000000000000 : ℝ)^7 := by
    have hnat : (153280919 : ℕ)^9*100000000000000^7 ≤ 53314770035991^7*250000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      153280919 250000000 53314770035991 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1586522441/10000000000 : ℝ)^9 ≤ (9375669337559/100000000000000 : ℝ)^7 := by
    have hnat : (1586522441 : ℕ)^9*100000000000000^7 ≤ 9375669337559^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1586522441 10000000000 9375669337559 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(464484489/1000000000 : ℝ), (153280919/250000000 : ℝ), (-1586522441/10000000000 : ℝ)] ![(37309560616857/100000000000000 : ℝ), (53314770035991/100000000000000 : ℝ), (9375669337559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(464484489/1000000000 : ℝ)|^9 ≤ (37309560616857/100000000000000 : ℝ)^7
        have hw : |(464484489/1000000000 : ℝ)|=(464484489/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(153280919/250000000 : ℝ)|^9 ≤ (53314770035991/100000000000000 : ℝ)^7
        have hw : |(153280919/250000000 : ℝ)|=(153280919/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1586522441/10000000000 : ℝ)|^9 ≤ (9375669337559/100000000000000 : ℝ)^7
        have hw : |(-1586522441/10000000000 : ℝ)|=(1586522441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s4_s4_13 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1455291117/2500000000 : ℝ)*x 0 + (1562246449/5000000000 : ℝ)*x 1 + (737243997/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1455291117/2500000000 : ℝ)^9 ≤ (9974699668359/20000000000000 : ℝ)^7 := by
    have hnat : (1455291117 : ℕ)^9*20000000000000^7 ≤ 9974699668359^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1455291117 2500000000 9974699668359 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1562246449/5000000000 : ℝ)^9 ≤ (22409431518997/100000000000000 : ℝ)^7 := by
    have hnat : (1562246449 : ℕ)^9*100000000000000^7 ≤ 22409431518997^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1562246449 5000000000 22409431518997 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (737243997/2000000000 : ℝ)^9 ≤ (27717070122953/100000000000000 : ℝ)^7 := by
    have hnat : (737243997 : ℕ)^9*100000000000000^7 ≤ 27717070122953^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      737243997 2000000000 27717070122953 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1455291117/2500000000 : ℝ), (1562246449/5000000000 : ℝ), (737243997/2000000000 : ℝ)] ![(9974699668359/20000000000000 : ℝ), (22409431518997/100000000000000 : ℝ), (27717070122953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1455291117/2500000000 : ℝ)|^9 ≤ (9974699668359/20000000000000 : ℝ)^7
        have hw : |(1455291117/2500000000 : ℝ)|=(1455291117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1562246449/5000000000 : ℝ)|^9 ≤ (22409431518997/100000000000000 : ℝ)^7
        have hw : |(1562246449/5000000000 : ℝ)|=(1562246449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(737243997/2000000000 : ℝ)|^9 ≤ (27717070122953/100000000000000 : ℝ)^7
        have hw : |(737243997/2000000000 : ℝ)|=(737243997/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s4_s4_14 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-1180555043/5000000000 : ℝ)*x 0 + (284070849/625000000 : ℝ)*x 1 + (1131634977/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1180555043/5000000000 : ℝ)^9 ≤ (122122762563/781250000000 : ℝ)^7 := by
    have hnat : (1180555043 : ℕ)^9*781250000000^7 ≤ 122122762563^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1180555043 5000000000 122122762563 781250000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (284070849/625000000 : ℝ)^9 ≤ (36282970706207/100000000000000 : ℝ)^7 := by
    have hnat : (284070849 : ℕ)^9*100000000000000^7 ≤ 36282970706207^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284070849 625000000 36282970706207 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1131634977/2000000000 : ℝ)^9 ≤ (48085315668219/100000000000000 : ℝ)^7 := by
    have hnat : (1131634977 : ℕ)^9*100000000000000^7 ≤ 48085315668219^7*2000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131634977 2000000000 48085315668219 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1180555043/5000000000 : ℝ), (284070849/625000000 : ℝ), (1131634977/2000000000 : ℝ)] ![(122122762563/781250000000 : ℝ), (36282970706207/100000000000000 : ℝ), (48085315668219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1180555043/5000000000 : ℝ)|^9 ≤ (122122762563/781250000000 : ℝ)^7
        have hw : |(-1180555043/5000000000 : ℝ)|=(1180555043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(284070849/625000000 : ℝ)|^9 ≤ (36282970706207/100000000000000 : ℝ)^7
        have hw : |(284070849/625000000 : ℝ)|=(284070849/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1131634977/2000000000 : ℝ)|^9 ≤ (48085315668219/100000000000000 : ℝ)^7
        have hw : |(1131634977/2000000000 : ℝ)|=(1131634977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s4_s4_15 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1150570937/2500000000 : ℝ)*x 0 + (-2466597987/10000000000 : ℝ)*x 1 + (5521222059/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1150570937/2500000000 : ℝ)^9 ≤ (3687058889509/10000000000000 : ℝ)^7 := by
    have hnat : (1150570937 : ℕ)^9*10000000000000^7 ≤ 3687058889509^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1150570937 2500000000 3687058889509 10000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2466597987/10000000000 : ℝ)^9 ≤ (16535304370461/100000000000000 : ℝ)^7 := by
    have hnat : (2466597987 : ℕ)^9*100000000000000^7 ≤ 16535304370461^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2466597987 10000000000 16535304370461 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5521222059/10000000000 : ℝ)^9 ≤ (46594106715081/100000000000000 : ℝ)^7 := by
    have hnat : (5521222059 : ℕ)^9*100000000000000^7 ≤ 46594106715081^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5521222059 10000000000 46594106715081 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1150570937/2500000000 : ℝ), (-2466597987/10000000000 : ℝ), (5521222059/10000000000 : ℝ)] ![(3687058889509/10000000000000 : ℝ), (16535304370461/100000000000000 : ℝ), (46594106715081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1150570937/2500000000 : ℝ)|^9 ≤ (3687058889509/10000000000000 : ℝ)^7
        have hw : |(1150570937/2500000000 : ℝ)|=(1150570937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2466597987/10000000000 : ℝ)|^9 ≤ (16535304370461/100000000000000 : ℝ)^7
        have hw : |(-2466597987/10000000000 : ℝ)|=(2466597987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5521222059/10000000000 : ℝ)|^9 ≤ (46594106715081/100000000000000 : ℝ)^7
        have hw : |(5521222059/10000000000 : ℝ)|=(5521222059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s4_s4_16 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (1198790919/2500000000 : ℝ)*x 0 + (5964766223/10000000000 : ℝ)*x 1 + (-1625129371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1198790919/2500000000 : ℝ)^9 ≤ (9717273492171/25000000000000 : ℝ)^7 := by
    have hnat : (1198790919 : ℕ)^9*25000000000000^7 ≤ 9717273492171^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198790919 2500000000 9717273492171 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5964766223/10000000000 : ℝ)^9 ≤ (12865221623553/25000000000000 : ℝ)^7 := by
    have hnat : (5964766223 : ℕ)^9*25000000000000^7 ≤ 12865221623553^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5964766223 10000000000 12865221623553 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1625129371/10000000000 : ℝ)^9 ≤ (604376219849/6250000000000 : ℝ)^7 := by
    have hnat : (1625129371 : ℕ)^9*6250000000000^7 ≤ 604376219849^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1625129371 10000000000 604376219849 6250000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1198790919/2500000000 : ℝ), (5964766223/10000000000 : ℝ), (-1625129371/10000000000 : ℝ)] ![(9717273492171/25000000000000 : ℝ), (12865221623553/25000000000000 : ℝ), (604376219849/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1198790919/2500000000 : ℝ)|^9 ≤ (9717273492171/25000000000000 : ℝ)^7
        have hw : |(1198790919/2500000000 : ℝ)|=(1198790919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5964766223/10000000000 : ℝ)|^9 ≤ (12865221623553/25000000000000 : ℝ)^7
        have hw : |(5964766223/10000000000 : ℝ)|=(5964766223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1625129371/10000000000 : ℝ)|^9 ≤ (604376219849/6250000000000 : ℝ)^7
        have hw : |(-1625129371/10000000000 : ℝ)|=(1625129371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s4_s4_20 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (5978242957/10000000000 : ℝ)*x 0 + (760073481/2500000000 : ℝ)*x 1 + (224135271/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5978242957/10000000000 : ℝ)^9 ≤ (51610425001621/100000000000000 : ℝ)^7 := by
    have hnat : (5978242957 : ℕ)^9*100000000000000^7 ≤ 51610425001621^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5978242957 10000000000 51610425001621 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (760073481/2500000000 : ℝ)^9 ≤ (4327201899853/20000000000000 : ℝ)^7 := by
    have hnat : (760073481 : ℕ)^9*20000000000000^7 ≤ 4327201899853^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      760073481 2500000000 4327201899853 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (224135271/625000000 : ℝ)^9 ≤ (13376782743999/50000000000000 : ℝ)^7 := by
    have hnat : (224135271 : ℕ)^9*50000000000000^7 ≤ 13376782743999^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      224135271 625000000 13376782743999 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5978242957/10000000000 : ℝ), (760073481/2500000000 : ℝ), (224135271/625000000 : ℝ)] ![(51610425001621/100000000000000 : ℝ), (4327201899853/20000000000000 : ℝ), (13376782743999/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5978242957/10000000000 : ℝ)|^9 ≤ (51610425001621/100000000000000 : ℝ)^7
        have hw : |(5978242957/10000000000 : ℝ)|=(5978242957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(760073481/2500000000 : ℝ)|^9 ≤ (4327201899853/20000000000000 : ℝ)^7
        have hw : |(760073481/2500000000 : ℝ)|=(760073481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(224135271/625000000 : ℝ)|^9 ≤ (13376782743999/50000000000000 : ℝ)^7
        have hw : |(224135271/625000000 : ℝ)|=(224135271/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s4_s4_21 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (-2368363037/10000000000 : ℝ)*x 0 + (4561629179/10000000000 : ℝ)*x 1 + (5637007917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2368363037/10000000000 : ℝ)^9 ≤ (7846739127871/50000000000000 : ℝ)^7 := by
    have hnat : (2368363037 : ℕ)^9*50000000000000^7 ≤ 7846739127871^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2368363037 10000000000 7846739127871 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4561629179/10000000000 : ℝ)^9 ≤ (18226181482047/50000000000000 : ℝ)^7 := by
    have hnat : (4561629179 : ℕ)^9*50000000000000^7 ≤ 18226181482047^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4561629179 10000000000 18226181482047 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5637007917/10000000000 : ℝ)^9 ≤ (23927079384073/50000000000000 : ℝ)^7 := by
    have hnat : (5637007917 : ℕ)^9*50000000000000^7 ≤ 23927079384073^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5637007917 10000000000 23927079384073 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2368363037/10000000000 : ℝ), (4561629179/10000000000 : ℝ), (5637007917/10000000000 : ℝ)] ![(7846739127871/50000000000000 : ℝ), (18226181482047/50000000000000 : ℝ), (23927079384073/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2368363037/10000000000 : ℝ)|^9 ≤ (7846739127871/50000000000000 : ℝ)^7
        have hw : |(-2368363037/10000000000 : ℝ)|=(2368363037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4561629179/10000000000 : ℝ)|^9 ≤ (18226181482047/50000000000000 : ℝ)^7
        have hw : |(4561629179/10000000000 : ℝ)|=(4561629179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5637007917/10000000000 : ℝ)|^9 ≤ (23927079384073/50000000000000 : ℝ)^7
        have hw : |(5637007917/10000000000 : ℝ)|=(5637007917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s4_s4_22 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4777724563/10000000000 : ℝ)*x 0 + (-149635087/625000000 : ℝ)*x 1 + (5410754813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4777724563/10000000000 : ℝ)^9 ≤ (7737488078427/20000000000000 : ℝ)^7 := by
    have hnat : (4777724563 : ℕ)^9*20000000000000^7 ≤ 7737488078427^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4777724563 10000000000 7737488078427 20000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (149635087/625000000 : ℝ)^9 ≤ (1989201142033/12500000000000 : ℝ)^7 := by
    have hnat : (149635087 : ℕ)^9*12500000000000^7 ≤ 1989201142033^7*625000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149635087 625000000 1989201142033 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410754813/10000000000 : ℝ)^9 ≤ (22699475227717/50000000000000 : ℝ)^7 := by
    have hnat : (5410754813 : ℕ)^9*50000000000000^7 ≤ 22699475227717^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410754813 10000000000 22699475227717 50000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4777724563/10000000000 : ℝ), (-149635087/625000000 : ℝ), (5410754813/10000000000 : ℝ)] ![(7737488078427/20000000000000 : ℝ), (1989201142033/12500000000000 : ℝ), (22699475227717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4777724563/10000000000 : ℝ)|^9 ≤ (7737488078427/20000000000000 : ℝ)^7
        have hw : |(4777724563/10000000000 : ℝ)|=(4777724563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-149635087/625000000 : ℝ)|^9 ≤ (1989201142033/12500000000000 : ℝ)^7
        have hw : |(-149635087/625000000 : ℝ)|=(149635087/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410754813/10000000000 : ℝ)|^9 ≤ (22699475227717/50000000000000 : ℝ)^7
        have hw : |(5410754813/10000000000 : ℝ)|=(5410754813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s4_s4_23 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (4603045299/10000000000 : ℝ)*x 0 + (6088631913/10000000000 : ℝ)*x 1 + (-426164423/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4603045299/10000000000 : ℝ)^9 ≤ (36878433307373/100000000000000 : ℝ)^7 := by
    have hnat : (4603045299 : ℕ)^9*100000000000000^7 ≤ 36878433307373^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4603045299 10000000000 36878433307373 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6088631913/10000000000 : ℝ)^9 ≤ (52838919148561/100000000000000 : ℝ)^7 := by
    have hnat : (6088631913 : ℕ)^9*100000000000000^7 ≤ 52838919148561^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6088631913 10000000000 52838919148561 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (426164423/2500000000 : ℝ)^9 ≤ (2570661880627/25000000000000 : ℝ)^7 := by
    have hnat : (426164423 : ℕ)^9*25000000000000^7 ≤ 2570661880627^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426164423 2500000000 2570661880627 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4603045299/10000000000 : ℝ), (6088631913/10000000000 : ℝ), (-426164423/2500000000 : ℝ)] ![(36878433307373/100000000000000 : ℝ), (52838919148561/100000000000000 : ℝ), (2570661880627/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4603045299/10000000000 : ℝ)|^9 ≤ (36878433307373/100000000000000 : ℝ)^7
        have hw : |(4603045299/10000000000 : ℝ)|=(4603045299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6088631913/10000000000 : ℝ)|^9 ≤ (52838919148561/100000000000000 : ℝ)^7
        have hw : |(6088631913/10000000000 : ℝ)|=(6088631913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-426164423/2500000000 : ℝ)|^9 ≤ (2570661880627/25000000000000 : ℝ)^7
        have hw : |(-426164423/2500000000 : ℝ)|=(426164423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c311061_s4_s4_27 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ)) (x : Fin 3 → ℝ) :
    (2999901603/5000000000 : ℝ)*x 0 + (3037527257/10000000000 : ℝ)*x 1 + (890955163/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2999901603/5000000000 : ℝ)^9 ≤ (12962464722517/25000000000000 : ℝ)^7 := by
    have hnat : (2999901603 : ℕ)^9*25000000000000^7 ≤ 12962464722517^7*5000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2999901603 5000000000 12962464722517 25000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3037527257/10000000000 : ℝ)^9 ≤ (2701337333001/12500000000000 : ℝ)^7 := by
    have hnat : (3037527257 : ℕ)^9*12500000000000^7 ≤ 2701337333001^7*10000000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3037527257 10000000000 2701337333001 12500000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (890955163/2500000000 : ℝ)^9 ≤ (26539442433569/100000000000000 : ℝ)^7 := by
    have hnat : (890955163 : ℕ)^9*100000000000000^7 ≤ 26539442433569^7*2500000000^9 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890955163 2500000000 26539442433569 100000000000000 9 7 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (9/2 : ℝ)) 9 7 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2999901603/5000000000 : ℝ), (3037527257/10000000000 : ℝ), (890955163/2500000000 : ℝ)] ![(12962464722517/25000000000000 : ℝ), (2701337333001/12500000000000 : ℝ), (26539442433569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2999901603/5000000000 : ℝ)|^9 ≤ (12962464722517/25000000000000 : ℝ)^7
        have hw : |(2999901603/5000000000 : ℝ)|=(2999901603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3037527257/10000000000 : ℝ)|^9 ≤ (2701337333001/12500000000000 : ℝ)^7
        have hw : |(3037527257/10000000000 : ℝ)|=(3037527257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(890955163/2500000000 : ℝ)|^9 ≤ (26539442433569/100000000000000 : ℝ)^7
        have hw : |(890955163/2500000000 : ℝ)|=(890955163/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c311061_s4 (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((14351/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14351/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34161/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(34161/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31369/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(31369/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((7197/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7197/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(913/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(913/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(523/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(523/3125 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (19517/25000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (19517/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (19517/25000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (19517/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (19517/25000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((-1 : ℝ)*(X 0 1+X 1 1)) ∧ ((-1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((-1 : ℝ)*pair X 2 1) ∧ ((-1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((-1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.2.1]
  have base59 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  rcases hprev3 with ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩
  have s4_pow0 : (14351/50000 : ℝ) ^ (71/16 : ℝ) ≤ (78616771706413741/20000000000000000000 : ℝ) := by
    have hpowers : (14351/50000 : ℝ)^71 ≤ (78616771706413741/20000000000000000000 : ℝ)^16 := by
      have hnat : (14351 : ℕ)^71*20000000000000000000^16 ≤ 78616771706413741^16*50000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14351 50000 78616771706413741 20000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14351/50000 : ℝ)) (X := (78616771706413741/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s4_corner0a : (20078616771706413741/20000000000000000000 : ℝ) ≤ (2502211193087823/2500000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (20078616771706413741/20000000000000000000 : ℝ)^16 ≤ (2502211193087823/2500000000000000 : ℝ)^71 := by
      have hnat : (20078616771706413741 : ℕ)^16*2500000000000000^71 ≤ 2502211193087823^71*20000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20078616771706413741 20000000000000000000 2502211193087823 2500000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502211193087823/2500000000000000 : ℝ)) (X := (20078616771706413741/20000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s4_corner0b : (10078616771706413741/10000000000000000000 : ℝ) ≤ (2504415689558043/2500000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (10078616771706413741/10000000000000000000 : ℝ)^16 ≤ (2504415689558043/2500000000000000 : ℝ)^71 := by
      have hnat : (10078616771706413741 : ℕ)^16*2500000000000000^71 ≤ 2504415689558043^71*10000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10078616771706413741 10000000000000000000 2504415689558043 2500000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2504415689558043/2500000000000000 : ℝ)) (X := (10078616771706413741/10000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s4_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(2211193087823/717550000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(110224823511/35877500000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (14351/50000 : ℝ)) (alpha := (2211193087823/717550000000000 : ℝ)) (beta := (110224823511/35877500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow0,s4_corner0a]) (by linarith only [s4_pow0,s4_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (14351/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(2211193087823/717550000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(110224823511/35877500000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow1 : (34161/100000 : ℝ) ^ (71/16 : ℝ) ≤ (851220213804944053/100000000000000000000 : ℝ) := by
    have hpowers : (34161/100000 : ℝ)^71 ≤ (851220213804944053/100000000000000000000 : ℝ)^16 := by
      have hnat : (34161 : ℕ)^71*100000000000000000000^16 ≤ 851220213804944053^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        34161 100000 851220213804944053 100000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (34161/100000 : ℝ)) (X := (851220213804944053/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s4_corner1a : (100851220213804944053/100000000000000000000 : ℝ) ≤ (5009559749934889/5000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (100851220213804944053/100000000000000000000 : ℝ)^16 ≤ (5009559749934889/5000000000000000 : ℝ)^71 := by
      have hnat : (100851220213804944053 : ℕ)^16*5000000000000000^71 ≤ 5009559749934889^71*100000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100851220213804944053 100000000000000000000 5009559749934889 5000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5009559749934889/5000000000000000 : ℝ)) (X := (100851220213804944053/100000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s4_corner1b : (50851220213804944053/50000000000000000000 : ℝ) ≤ (5019057198187547/5000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (50851220213804944053/50000000000000000000 : ℝ)^16 ≤ (5019057198187547/5000000000000000 : ℝ)^71 := by
      have hnat : (50851220213804944053 : ℕ)^16*5000000000000000^71 ≤ 5019057198187547^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50851220213804944053 50000000000000000000 5019057198187547 5000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5019057198187547/5000000000000000 : ℝ)) (X := (50851220213804944053/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s4_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(9559749934889/1708050000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(4748724126329/854025000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (34161/100000 : ℝ)) (alpha := (9559749934889/1708050000000000 : ℝ)) (beta := (4748724126329/854025000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow1,s4_corner1a]) (by linarith only [s4_pow1,s4_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (34161/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(9559749934889/1708050000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(4748724126329/854025000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s4_pow2 : (31369/100000 : ℝ) ^ (71/16 : ℝ) ≤ (291535701538429161/50000000000000000000 : ℝ) := by
    have hpowers : (31369/100000 : ℝ)^71 ≤ (291535701538429161/50000000000000000000 : ℝ)^16 := by
      have hnat : (31369 : ℕ)^71*50000000000000000000^16 ≤ 291535701538429161^16*100000^71 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        31369 100000 291535701538429161 50000000000000000000 71 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (31369/100000 : ℝ)) (X := (291535701538429161/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s4_corner2a : (50291535701538429161/50000000000000000000 : ℝ) ≤ (10013110064961013/10000000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (50291535701538429161/50000000000000000000 : ℝ)^16 ≤ (10013110064961013/10000000000000000 : ℝ)^71 := by
      have hnat : (50291535701538429161 : ℕ)^16*10000000000000000^71 ≤ 10013110064961013^71*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50291535701538429161 50000000000000000000 10013110064961013 10000000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10013110064961013/10000000000000000 : ℝ)) (X := (50291535701538429161/50000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have s4_corner2b : (25291535701538429161/25000000000000000000 : ℝ) ≤ (626635086864137/625000000000000 : ℝ) ^ (71/16 : ℝ) := by
    have hpowers : (25291535701538429161/25000000000000000000 : ℝ)^16 ≤ (626635086864137/625000000000000 : ℝ)^71 := by
      have hnat : (25291535701538429161 : ℕ)^16*625000000000000^71 ≤ 626635086864137^71*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25291535701538429161 25000000000000000000 626635086864137 625000000000000 16 71 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (626635086864137/625000000000000 : ℝ)) (X := (25291535701538429161/25000000000000000000 : ℝ)) (by norm_num) 71 16 (by norm_num) hpowers
    exact h
  have major_s4_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(13110064961013/3136900000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(13051324865179/3136900000000000 : ℝ)*((-1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (71/16 : ℝ)) (rho := (31369/100000 : ℝ)) (alpha := (13110064961013/3136900000000000 : ℝ)) (beta := (13051324865179/3136900000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s4_pow2,s4_corner2a]) (by linarith only [s4_pow2,s4_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (31369/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s3_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(13110064961013/3136900000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(13051324865179/3136900000000000 : ℝ)*((-1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s4_0 : ((-2478411167/10000000000 : ℝ)*X 0 0+(89895061/200000000 : ℝ)*X 0 1+(1122670193/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s4_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_1 : ((4667119309/10000000000 : ℝ)*X 1 0+(-2503409381/10000000000 : ℝ)*X 1 1+(271501473/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s4_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_2 : ((2338652771/5000000000 : ℝ)*X 2 0+(6012053853/10000000000 : ℝ)*X 2 1+(-214470341/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s4_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_6 : ((2914569373/5000000000 : ℝ)*X 0 0+(1556717247/5000000000 : ℝ)*X 0 1+(3687674709/10000000000 : ℝ)*X 0 2+(2914569373/5000000000 : ℝ)*X 1 0+(1556717247/5000000000 : ℝ)*X 1 1+(3687674709/10000000000 : ℝ)*X 1 2+(2914569373/5000000000 : ℝ)*X 2 0+(1556717247/5000000000 : ℝ)*X 2 1+(3687674709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s4_s4_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_7 : ((-1237558853/5000000000 : ℝ)*X 0 0+(4496387063/10000000000 : ℝ)*X 0 1+(5614424289/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s4_s4_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_8 : ((2317328991/5000000000 : ℝ)*X 1 0+(-475754413/2000000000 : ℝ)*X 1 1+(5559826929/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s4_s4_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_9 : ((464484489/1000000000 : ℝ)*X 2 0+(153280919/250000000 : ℝ)*X 2 1+(-1586522441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s4_s4_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_13 : ((1455291117/2500000000 : ℝ)*X 0 0+(1562246449/5000000000 : ℝ)*X 0 1+(737243997/2000000000 : ℝ)*X 0 2+(1455291117/2500000000 : ℝ)*X 1 0+(1562246449/5000000000 : ℝ)*X 1 1+(737243997/2000000000 : ℝ)*X 1 2+(1455291117/2500000000 : ℝ)*X 2 0+(1562246449/5000000000 : ℝ)*X 2 1+(737243997/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s4_s4_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_14 : ((-1180555043/5000000000 : ℝ)*X 0 0+(284070849/625000000 : ℝ)*X 0 1+(1131634977/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s4_s4_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_15 : ((1150570937/2500000000 : ℝ)*X 1 0+(-2466597987/10000000000 : ℝ)*X 1 1+(5521222059/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s4_s4_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_16 : ((1198790919/2500000000 : ℝ)*X 2 0+(5964766223/10000000000 : ℝ)*X 2 1+(-1625129371/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s4_s4_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_20 : ((5978242957/10000000000 : ℝ)*X 0 0+(760073481/2500000000 : ℝ)*X 0 1+(224135271/625000000 : ℝ)*X 0 2+(5978242957/10000000000 : ℝ)*X 1 0+(760073481/2500000000 : ℝ)*X 1 1+(224135271/625000000 : ℝ)*X 1 2+(5978242957/10000000000 : ℝ)*X 2 0+(760073481/2500000000 : ℝ)*X 2 1+(224135271/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s4_s4_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_21 : ((-2368363037/10000000000 : ℝ)*X 0 0+(4561629179/10000000000 : ℝ)*X 0 1+(5637007917/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s4_s4_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_22 : ((4777724563/10000000000 : ℝ)*X 1 0+(-149635087/625000000 : ℝ)*X 1 1+(5410754813/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s4_s4_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_23 : ((4603045299/10000000000 : ℝ)*X 2 0+(6088631913/10000000000 : ℝ)*X 2 1+(-426164423/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s4_s4_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s4_27 : ((2999901603/5000000000 : ℝ)*X 0 0+(3037527257/10000000000 : ℝ)*X 0 1+(890955163/2500000000 : ℝ)*X 0 2+(2999901603/5000000000 : ℝ)*X 1 0+(3037527257/10000000000 : ℝ)*X 1 1+(890955163/2500000000 : ℝ)*X 1 2+(2999901603/5000000000 : ℝ)*X 2 0+(3037527257/10000000000 : ℝ)*X 2 1+(890955163/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c311061_s4_s4_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s4_0 : (0 : ℝ) ≤ ((7197/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7197/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (52355381728892754178636181/4085370925000000000000000000000 : ℝ) := by norm_num
    linear_combination (1164374853/8000000000 : ℝ)*(base40) + (320523072297/62500000000 : ℝ)*(base59) + (28485058041653/1000000000000 : ℝ)*(major_s4_0) + (28485058041653/1000000000000 : ℝ)*(major_s4_1) + (28485058041653/1000000000000 : ℝ)*(major_s4_2) + (33604832749/200000000000 : ℝ)*(sp_s4_0) + (43193269/1000000000000 : ℝ)*(sp_s4_1) + (19732554955123/500000000000 : ℝ)*(sp_s4_7) + (396364647681/10000000000 : ℝ)*(sp_s4_8) + (9909267323857/250000000000 : ℝ)*(sp_s4_9) + (17332159832583/1000000000000 : ℝ)*(sp_s4_13) + (4817904951/1000000000000 : ℝ)*(sp_s4_14) + (361004393/250000000000 : ℝ)*(sp_s4_15) + (441341757/500000000000 : ℝ)*(sp_s4_23) + (17332159832583/1000000000000 : ℝ)*(f.failure) + (19818975989471/500000000000 : ℝ)*(f.sum) + (1100224864944852551/21431928180000000000000000000000 : ℝ)*base62 + (337913372371573/3136900000000000000000000000 : ℝ)*base65 + (712643678573071/1708050000000000000000000000 : ℝ)*base66 + (97061290146999/3136900000000000000000000000 : ℝ)*base69 + (2303602758559363/70893940000000000000000000000 : ℝ)*base70 + (58097569576039/143510000000000000000000000 : ℝ)*base73 + (737846380750733/1708050000000000000000000000 : ℝ)*base74 + (492445452102061/717550000000000000000000000 : ℝ)*base76 + (5913819540526257289/24512225550000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (12721/25000000000000000 : ℝ)*base87 + (12721/25000000000000000 : ℝ)*base89 + (12721/25000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s4_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(913/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(913/5000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (371599738346768867193007541/40363464739000000000000000000000 : ℝ) := by norm_num
    linear_combination (15997853/1000000000000 : ℝ)*(base39) + (162948693801/250000000000 : ℝ)*(base40) + (26695602403/3906250000 : ℝ)*(base59) + (9834054040247/250000000000 : ℝ)*(major_s4_0) + (9834054040247/250000000000 : ℝ)*(major_s4_1) + (9834054040247/250000000000 : ℝ)*(major_s4_2) + (615544243/1000000000000 : ℝ)*(sp_s4_0) + (882900853/500000000000 : ℝ)*(sp_s4_1) + (120063069/250000000000 : ℝ)*(sp_s4_6) + (1130906171/500000000000 : ℝ)*(sp_s4_8) + (27368552167777/500000000000 : ℝ)*(sp_s4_14) + (54733692265749/1000000000000 : ℝ)*(sp_s4_15) + (54737719879797/1000000000000 : ℝ)*(sp_s4_16) + (149588932007/6250000000 : ℝ)*(sp_s4_20) + (5983677343349/250000000000 : ℝ)*(f.failure) + (54737719879797/1000000000000 : ℝ)*(f.sum) + (3040941844133026909/10715964090000000000000000000000 : ℝ)*base62 + (2830106375297/196056250000000000000000000 : ℝ)*base64 + (430096797404041/1708050000000000000000000000 : ℝ)*base66 + (143489995080937/392112500000000000000000000 : ℝ)*base68 + (10524652799733967/35446970000000000000000000000 : ℝ)*base70 + (18025426310249/143510000000000000000000000 : ℝ)*base73 + (78371995264201/213506250000000000000000000 : ℝ)*base74 + (415624232221901/717550000000000000000000000 : ℝ)*base76 + (4923141925251813529/24512225550000000000000000000000 : ℝ)*base79 + (5363/6250000000000000 : ℝ)*base87 + (5363/6250000000000000 : ℝ)*base89 + (5363/6250000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s4_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(523/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(523/3125 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (3053379044673842839095699/177234850000000000000000000000 : ℝ) := by norm_num
    linear_combination (140898075251/125000000000 : ℝ)*(base40) + (232713/50000000000 : ℝ)*(base50) + (6851630668751/1000000000000 : ℝ)*(base59) + (38874404348433/1000000000000 : ℝ)*(major_s4_0) + (38874404348433/1000000000000 : ℝ)*(major_s4_1) + (38874404348433/1000000000000 : ℝ)*(major_s4_2) + (613694173/200000000000 : ℝ)*(sp_s4_1) + (201560993/250000000000 : ℝ)*(sp_s4_2) + (77679947/25000000000 : ℝ)*(sp_s4_7) + (131652083/500000000000 : ℝ)*(sp_s4_9) + (27045991345567/500000000000 : ℝ)*(sp_s4_21) + (13523005354537/250000000000 : ℝ)*(sp_s4_22) + (13523505085219/250000000000 : ℝ)*(sp_s4_23) + (23653713065223/1000000000000 : ℝ)*(sp_s4_27) + (23653713065223/1000000000000 : ℝ)*(f.failure) + (27047544944507/500000000000 : ℝ)*(f.sum) + (193634151692316077/1428795212000000000000000000000 : ℝ)*base63 + (2420291082624037/3136900000000000000000000000 : ℝ)*base64 + (12433456169719/71168750000000000000000000 : ℝ)*base66 + (813977023914199/3136900000000000000000000000 : ℝ)*base69 + (34620318207171209/70893940000000000000000000000 : ℝ)*base70 + (3337681152679/17938750000000000000000000 : ℝ)*base73 + (208259622046331/569350000000000000000000000 : ℝ)*base74 + (113732490175883/358775000000000000000000000 : ℝ)*base76 + (35781116422946467/127667841406250000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base82 + (7599/25000000000000000 : ℝ)*base86 + (7599/25000000000000000 : ℝ)*base88 + (7599/25000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s4_0,ratio_s4_1,ratio_s4_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (71/16 : ℝ) ≤ p) (hpb : p ≤ (9/2 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (41087/25000 : ℝ) (89829/50000 : ℝ) (19517/25000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, false, true]])
    (hprev3 : (0 : ℝ) ≤ ((14351/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(14351/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(34161/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(34161/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(31369/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(31369/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((7197/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(7197/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(913/5000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(913/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(523/3125 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(523/3125 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c311061_s4 p hpa hpb X hX hprev3

#print axioms solution
