-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c314031_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:45:22.204929+00:00
-- url     : https://prove2.me/submissions/a174cc5f-55f8-47c1-9b1d-c9720c977c27

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
theorem collision_support_c314031_s1_s1_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-416791013/1250000000 : ℝ)*x 0 + (2742413571/5000000000 : ℝ)*x 1 + (3700856293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (416791013/1250000000 : ℝ)^19 ≤ (24877718830761/100000000000000 : ℝ)^15 := by
    have hnat : (416791013 : ℕ)^19*100000000000000^15 ≤ 24877718830761^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416791013 1250000000 24877718830761 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2742413571/5000000000 : ℝ)^19 ≤ (46731142296971/100000000000000 : ℝ)^15 := by
    have hnat : (2742413571 : ℕ)^19*100000000000000^15 ≤ 46731142296971^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742413571 5000000000 46731142296971 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3700856293/10000000000 : ℝ)^19 ≤ (28391138860329/100000000000000 : ℝ)^15 := by
    have hnat : (3700856293 : ℕ)^19*100000000000000^15 ≤ 28391138860329^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3700856293 10000000000 28391138860329 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-416791013/1250000000 : ℝ), (2742413571/5000000000 : ℝ), (3700856293/10000000000 : ℝ)] ![(24877718830761/100000000000000 : ℝ), (46731142296971/100000000000000 : ℝ), (28391138860329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-416791013/1250000000 : ℝ)|^19 ≤ (24877718830761/100000000000000 : ℝ)^15
        have hw : |(-416791013/1250000000 : ℝ)|=(416791013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2742413571/5000000000 : ℝ)|^19 ≤ (46731142296971/100000000000000 : ℝ)^15
        have hw : |(2742413571/5000000000 : ℝ)|=(2742413571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3700856293/10000000000 : ℝ)|^19 ≤ (28391138860329/100000000000000 : ℝ)^15
        have hw : |(3700856293/10000000000 : ℝ)|=(3700856293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314031_s1_s1_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (5933064189/10000000000 : ℝ)*x 0 + (-590335497/10000000000 : ℝ)*x 1 + (672513843/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5933064189/10000000000 : ℝ)^19 ≤ (10324050537007/20000000000000 : ℝ)^15 := by
    have hnat : (5933064189 : ℕ)^19*20000000000000^15 ≤ 10324050537007^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5933064189 10000000000 10324050537007 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (590335497/10000000000 : ℝ)^19 ≤ (693956018159/25000000000000 : ℝ)^15 := by
    have hnat : (590335497 : ℕ)^19*25000000000000^15 ≤ 693956018159^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      590335497 10000000000 693956018159 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (672513843/1250000000 : ℝ)^19 ≤ (45603923239361/100000000000000 : ℝ)^15 := by
    have hnat : (672513843 : ℕ)^19*100000000000000^15 ≤ 45603923239361^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672513843 1250000000 45603923239361 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5933064189/10000000000 : ℝ), (-590335497/10000000000 : ℝ), (672513843/1250000000 : ℝ)] ![(10324050537007/20000000000000 : ℝ), (693956018159/25000000000000 : ℝ), (45603923239361/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5933064189/10000000000 : ℝ)|^19 ≤ (10324050537007/20000000000000 : ℝ)^15
        have hw : |(5933064189/10000000000 : ℝ)|=(5933064189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-590335497/10000000000 : ℝ)|^19 ≤ (693956018159/25000000000000 : ℝ)^15
        have hw : |(-590335497/10000000000 : ℝ)|=(590335497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(672513843/1250000000 : ℝ)|^19 ≤ (45603923239361/100000000000000 : ℝ)^15
        have hw : |(672513843/1250000000 : ℝ)|=(672513843/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314031_s1_s1_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3088000781/10000000000 : ℝ)*x 0 + (5937200087/10000000000 : ℝ)*x 1 + (-3427451279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3088000781/10000000000 : ℝ)^19 ≤ (22573108820747/100000000000000 : ℝ)^15 := by
    have hnat : (3088000781 : ℕ)^19*100000000000000^15 ≤ 22573108820747^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3088000781 10000000000 22573108820747 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5937200087/10000000000 : ℝ)^19 ≤ (10333167361481/20000000000000 : ℝ)^15 := by
    have hnat : (5937200087 : ℕ)^19*20000000000000^15 ≤ 10333167361481^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5937200087 10000000000 10333167361481 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3427451279/10000000000 : ℝ)^19 ≤ (25761054359767/100000000000000 : ℝ)^15 := by
    have hnat : (3427451279 : ℕ)^19*100000000000000^15 ≤ 25761054359767^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3427451279 10000000000 25761054359767 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3088000781/10000000000 : ℝ), (5937200087/10000000000 : ℝ), (-3427451279/10000000000 : ℝ)] ![(22573108820747/100000000000000 : ℝ), (10333167361481/20000000000000 : ℝ), (25761054359767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3088000781/10000000000 : ℝ)|^19 ≤ (22573108820747/100000000000000 : ℝ)^15
        have hw : |(3088000781/10000000000 : ℝ)|=(3088000781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5937200087/10000000000 : ℝ)|^19 ≤ (10333167361481/20000000000000 : ℝ)^15
        have hw : |(5937200087/10000000000 : ℝ)|=(5937200087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3427451279/10000000000 : ℝ)|^19 ≤ (25761054359767/100000000000000 : ℝ)^15
        have hw : |(-3427451279/10000000000 : ℝ)|=(3427451279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314031_s1_s1_4 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (0 : ℝ)*x 0 + (1 : ℝ)*x 1 + (0 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (0 : ℝ)^19 ≤ (0 : ℝ)^15 := by
    have hnat : (0 : ℕ)^19*1^15 ≤ 0^15*1^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1 : ℝ)^19 ≤ (1 : ℝ)^15 := by
    have hnat : (1 : ℕ)^19*1^15 ≤ 1^15*1^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1 1 1 1 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (0 : ℝ)^19 ≤ (0 : ℝ)^15 := by
    have hnat : (0 : ℕ)^19*1^15 ≤ 0^15*1^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      0 1 0 1 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] ![(0 : ℝ), (1 : ℝ), (0 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(0 : ℝ)|^19 ≤ (0 : ℝ)^15
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1 : ℝ)|^19 ≤ (1 : ℝ)^15
        have hw : |(1 : ℝ)|=(1 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(0 : ℝ)|^19 ≤ (0 : ℝ)^15
        have hw : |(0 : ℝ)|=(0 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314031_s1_s1_6 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4036839229/10000000000 : ℝ)*x 0 + (2440107099/5000000000 : ℝ)*x 1 + (3660611349/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4036839229/10000000000 : ℝ)^19 ≤ (1584732065407/5000000000000 : ℝ)^15 := by
    have hnat : (4036839229 : ℕ)^19*5000000000000^15 ≤ 1584732065407^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4036839229 10000000000 1584732065407 5000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2440107099/5000000000 : ℝ)^19 ≤ (4030472105989/10000000000000 : ℝ)^15 := by
    have hnat : (2440107099 : ℕ)^19*10000000000000^15 ≤ 4030472105989^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2440107099 5000000000 4030472105989 10000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3660611349/10000000000 : ℝ)^19 ≤ (14000318807713/50000000000000 : ℝ)^15 := by
    have hnat : (3660611349 : ℕ)^19*50000000000000^15 ≤ 14000318807713^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3660611349 10000000000 14000318807713 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4036839229/10000000000 : ℝ), (2440107099/5000000000 : ℝ), (3660611349/10000000000 : ℝ)] ![(1584732065407/5000000000000 : ℝ), (4030472105989/10000000000000 : ℝ), (14000318807713/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4036839229/10000000000 : ℝ)|^19 ≤ (1584732065407/5000000000000 : ℝ)^15
        have hw : |(4036839229/10000000000 : ℝ)|=(4036839229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2440107099/5000000000 : ℝ)|^19 ≤ (4030472105989/10000000000000 : ℝ)^15
        have hw : |(2440107099/5000000000 : ℝ)|=(2440107099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3660611349/10000000000 : ℝ)|^19 ≤ (14000318807713/50000000000000 : ℝ)^15
        have hw : |(3660611349/10000000000 : ℝ)|=(3660611349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314031_s1_s1_7 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-13119287/39062500 : ℝ)*x 0 + (5490460747/10000000000 : ℝ)*x 1 + (1835499199/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13119287/39062500 : ℝ)^19 ≤ (25106735716099/100000000000000 : ℝ)^15 := by
    have hnat : (13119287 : ℕ)^19*100000000000000^15 ≤ 25106735716099^15*39062500^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13119287 39062500 25106735716099 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5490460747/10000000000 : ℝ)^19 ≤ (46791949026373/100000000000000 : ℝ)^15 := by
    have hnat : (5490460747 : ℕ)^19*100000000000000^15 ≤ 46791949026373^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5490460747 10000000000 46791949026373 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1835499199/5000000000 : ℝ)^19 ≤ (3512664405741/12500000000000 : ℝ)^15 := by
    have hnat : (1835499199 : ℕ)^19*12500000000000^15 ≤ 3512664405741^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1835499199 5000000000 3512664405741 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13119287/39062500 : ℝ), (5490460747/10000000000 : ℝ), (1835499199/5000000000 : ℝ)] ![(25106735716099/100000000000000 : ℝ), (46791949026373/100000000000000 : ℝ), (3512664405741/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13119287/39062500 : ℝ)|^19 ≤ (25106735716099/100000000000000 : ℝ)^15
        have hw : |(-13119287/39062500 : ℝ)|=(13119287/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5490460747/10000000000 : ℝ)|^19 ≤ (46791949026373/100000000000000 : ℝ)^15
        have hw : |(5490460747/10000000000 : ℝ)|=(5490460747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1835499199/5000000000 : ℝ)|^19 ≤ (3512664405741/12500000000000 : ℝ)^15
        have hw : |(1835499199/5000000000 : ℝ)|=(1835499199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314031_s1_s1_8 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2862897889/5000000000 : ℝ)*x 0 + (-3501311/5000000000 : ℝ)*x 1 + (1461055751/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2862897889/5000000000 : ℝ)^19 ≤ (1973870878373/4000000000000 : ℝ)^15 := by
    have hnat : (2862897889 : ℕ)^19*4000000000000^15 ≤ 1973870878373^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2862897889 5000000000 1973870878373 4000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3501311/5000000000 : ℝ)^19 ≤ (2523114009/25000000000000 : ℝ)^15 := by
    have hnat : (3501311 : ℕ)^19*25000000000000^15 ≤ 2523114009^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3501311 5000000000 2523114009 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1461055751/2500000000 : ℝ)^19 ≤ (25321567787921/50000000000000 : ℝ)^15 := by
    have hnat : (1461055751 : ℕ)^19*50000000000000^15 ≤ 25321567787921^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1461055751 2500000000 25321567787921 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2862897889/5000000000 : ℝ), (-3501311/5000000000 : ℝ), (1461055751/2500000000 : ℝ)] ![(1973870878373/4000000000000 : ℝ), (2523114009/25000000000000 : ℝ), (25321567787921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2862897889/5000000000 : ℝ)|^19 ≤ (1973870878373/4000000000000 : ℝ)^15
        have hw : |(2862897889/5000000000 : ℝ)|=(2862897889/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3501311/5000000000 : ℝ)|^19 ≤ (2523114009/25000000000000 : ℝ)^15
        have hw : |(-3501311/5000000000 : ℝ)|=(3501311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1461055751/2500000000 : ℝ)|^19 ≤ (25321567787921/50000000000000 : ℝ)^15
        have hw : |(1461055751/2500000000 : ℝ)|=(1461055751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314031_s1_s1_9 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2749772163/10000000000 : ℝ)*x 0 + (410410753/625000000 : ℝ)*x 1 + (-3005596719/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2749772163/10000000000 : ℝ)^19 ≤ (19488384255383/100000000000000 : ℝ)^15 := by
    have hnat : (2749772163 : ℕ)^19*100000000000000^15 ≤ 19488384255383^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2749772163 10000000000 19488384255383 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (410410753/625000000 : ℝ)^19 ≤ (58698774916963/100000000000000 : ℝ)^15 := by
    have hnat : (410410753 : ℕ)^19*100000000000000^15 ≤ 58698774916963^15*625000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410410753 625000000 58698774916963 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3005596719/10000000000 : ℝ)^19 ≤ (5453210204947/25000000000000 : ℝ)^15 := by
    have hnat : (3005596719 : ℕ)^19*25000000000000^15 ≤ 5453210204947^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3005596719 10000000000 5453210204947 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2749772163/10000000000 : ℝ), (410410753/625000000 : ℝ), (-3005596719/10000000000 : ℝ)] ![(19488384255383/100000000000000 : ℝ), (58698774916963/100000000000000 : ℝ), (5453210204947/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2749772163/10000000000 : ℝ)|^19 ≤ (19488384255383/100000000000000 : ℝ)^15
        have hw : |(2749772163/10000000000 : ℝ)|=(2749772163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(410410753/625000000 : ℝ)|^19 ≤ (58698774916963/100000000000000 : ℝ)^15
        have hw : |(410410753/625000000 : ℝ)|=(410410753/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3005596719/10000000000 : ℝ)|^19 ≤ (5453210204947/25000000000000 : ℝ)^15
        have hw : |(-3005596719/10000000000 : ℝ)|=(3005596719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314031_s1_s1_12 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (470974417/1250000000 : ℝ)*x 0 + (2480452603/5000000000 : ℝ)*x 1 + (961431259/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (470974417/1250000000 : ℝ)^19 ≤ (7260790856727/25000000000000 : ℝ)^15 := by
    have hnat : (470974417 : ℕ)^19*25000000000000^15 ≤ 7260790856727^15*1250000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      470974417 1250000000 7260790856727 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2480452603/5000000000 : ℝ)^19 ≤ (20575347578739/50000000000000 : ℝ)^15 := by
    have hnat : (2480452603 : ℕ)^19*50000000000000^15 ≤ 20575347578739^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2480452603 5000000000 20575347578739 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (961431259/2500000000 : ℝ)^19 ≤ (29806141402277/100000000000000 : ℝ)^15 := by
    have hnat : (961431259 : ℕ)^19*100000000000000^15 ≤ 29806141402277^15*2500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961431259 2500000000 29806141402277 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(470974417/1250000000 : ℝ), (2480452603/5000000000 : ℝ), (961431259/2500000000 : ℝ)] ![(7260790856727/25000000000000 : ℝ), (20575347578739/50000000000000 : ℝ), (29806141402277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(470974417/1250000000 : ℝ)|^19 ≤ (7260790856727/25000000000000 : ℝ)^15
        have hw : |(470974417/1250000000 : ℝ)|=(470974417/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2480452603/5000000000 : ℝ)|^19 ≤ (20575347578739/50000000000000 : ℝ)^15
        have hw : |(2480452603/5000000000 : ℝ)|=(2480452603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(961431259/2500000000 : ℝ)|^19 ≤ (29806141402277/100000000000000 : ℝ)^15
        have hw : |(961431259/2500000000 : ℝ)|=(961431259/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314031_s1_s1_13 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-343828481/1000000000 : ℝ)*x 0 + (458891061/1000000000 : ℝ)*x 1 + (4547253017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (343828481/1000000000 : ℝ)^19 ≤ (3233029652619/12500000000000 : ℝ)^15 := by
    have hnat : (343828481 : ℕ)^19*12500000000000^15 ≤ 3233029652619^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343828481 1000000000 3233029652619 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (458891061/1000000000 : ℝ)^19 ≤ (4660245942747/12500000000000 : ℝ)^15 := by
    have hnat : (458891061 : ℕ)^19*12500000000000^15 ≤ 4660245942747^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      458891061 1000000000 4660245942747 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4547253017/10000000000 : ℝ)^19 ≤ (18426897611813/50000000000000 : ℝ)^15 := by
    have hnat : (4547253017 : ℕ)^19*50000000000000^15 ≤ 18426897611813^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4547253017 10000000000 18426897611813 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-343828481/1000000000 : ℝ), (458891061/1000000000 : ℝ), (4547253017/10000000000 : ℝ)] ![(3233029652619/12500000000000 : ℝ), (4660245942747/12500000000000 : ℝ), (18426897611813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-343828481/1000000000 : ℝ)|^19 ≤ (3233029652619/12500000000000 : ℝ)^15
        have hw : |(-343828481/1000000000 : ℝ)|=(343828481/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(458891061/1000000000 : ℝ)|^19 ≤ (4660245942747/12500000000000 : ℝ)^15
        have hw : |(458891061/1000000000 : ℝ)|=(458891061/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4547253017/10000000000 : ℝ)|^19 ≤ (18426897611813/50000000000000 : ℝ)^15
        have hw : |(4547253017/10000000000 : ℝ)|=(4547253017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314031_s1_s1_14 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (3599802731/5000000000 : ℝ)*x 0 + (-438161831/10000000000 : ℝ)*x 1 + (4081619601/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3599802731/5000000000 : ℝ)^19 ≤ (65956512485831/100000000000000 : ℝ)^15 := by
    have hnat : (3599802731 : ℕ)^19*100000000000000^15 ≤ 65956512485831^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3599802731 5000000000 65956512485831 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (438161831/10000000000 : ℝ)^19 ≤ (380569298601/20000000000000 : ℝ)^15 := by
    have hnat : (438161831 : ℕ)^19*20000000000000^15 ≤ 380569298601^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438161831 10000000000 380569298601 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4081619601/10000000000 : ℝ)^19 ≤ (8035160252261/25000000000000 : ℝ)^15 := by
    have hnat : (4081619601 : ℕ)^19*25000000000000^15 ≤ 8035160252261^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4081619601 10000000000 8035160252261 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3599802731/5000000000 : ℝ), (-438161831/10000000000 : ℝ), (4081619601/10000000000 : ℝ)] ![(65956512485831/100000000000000 : ℝ), (380569298601/20000000000000 : ℝ), (8035160252261/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3599802731/5000000000 : ℝ)|^19 ≤ (65956512485831/100000000000000 : ℝ)^15
        have hw : |(3599802731/5000000000 : ℝ)|=(3599802731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-438161831/10000000000 : ℝ)|^19 ≤ (380569298601/20000000000000 : ℝ)^15
        have hw : |(-438161831/10000000000 : ℝ)|=(438161831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4081619601/10000000000 : ℝ)|^19 ≤ (8035160252261/25000000000000 : ℝ)^15
        have hw : |(4081619601/10000000000 : ℝ)|=(4081619601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314031_s1_s1_15 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (1208919033/5000000000 : ℝ)*x 0 + (3232667491/5000000000 : ℝ)*x 1 + (-107521529/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1208919033/5000000000 : ℝ)^19 ≤ (16557997027279/100000000000000 : ℝ)^15 := by
    have hnat : (1208919033 : ℕ)^19*100000000000000^15 ≤ 16557997027279^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1208919033 5000000000 16557997027279 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3232667491/5000000000 : ℝ)^19 ≤ (28777428101181/50000000000000 : ℝ)^15 := by
    have hnat : (3232667491 : ℕ)^19*50000000000000^15 ≤ 28777428101181^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3232667491 5000000000 28777428101181 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107521529/312500000 : ℝ)^19 ≤ (6471786691021/25000000000000 : ℝ)^15 := by
    have hnat : (107521529 : ℕ)^19*25000000000000^15 ≤ 6471786691021^15*312500000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107521529 312500000 6471786691021 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1208919033/5000000000 : ℝ), (3232667491/5000000000 : ℝ), (-107521529/312500000 : ℝ)] ![(16557997027279/100000000000000 : ℝ), (28777428101181/50000000000000 : ℝ), (6471786691021/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1208919033/5000000000 : ℝ)|^19 ≤ (16557997027279/100000000000000 : ℝ)^15
        have hw : |(1208919033/5000000000 : ℝ)|=(1208919033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3232667491/5000000000 : ℝ)|^19 ≤ (28777428101181/50000000000000 : ℝ)^15
        have hw : |(3232667491/5000000000 : ℝ)|=(3232667491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-107521529/312500000 : ℝ)|^19 ≤ (6471786691021/25000000000000 : ℝ)^15
        have hw : |(-107521529/312500000 : ℝ)|=(107521529/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314031_s1_s1_19 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (2539805949/10000000000 : ℝ)*x 0 + (4981573163/10000000000 : ℝ)*x 1 + (197896551/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2539805949/10000000000 : ℝ)^19 ≤ (3524606799719/20000000000000 : ℝ)^15 := by
    have hnat : (2539805949 : ℕ)^19*20000000000000^15 ≤ 3524606799719^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2539805949 10000000000 3524606799719 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4981573163/10000000000 : ℝ)^19 ≤ (8273594763321/20000000000000 : ℝ)^15 := by
    have hnat : (4981573163 : ℕ)^19*20000000000000^15 ≤ 8273594763321^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4981573163 10000000000 8273594763321 20000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (197896551/400000000 : ℝ)^19 ≤ (10252248043467/25000000000000 : ℝ)^15 := by
    have hnat : (197896551 : ℕ)^19*25000000000000^15 ≤ 10252248043467^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197896551 400000000 10252248043467 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2539805949/10000000000 : ℝ), (4981573163/10000000000 : ℝ), (197896551/400000000 : ℝ)] ![(3524606799719/20000000000000 : ℝ), (8273594763321/20000000000000 : ℝ), (10252248043467/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2539805949/10000000000 : ℝ)|^19 ≤ (3524606799719/20000000000000 : ℝ)^15
        have hw : |(2539805949/10000000000 : ℝ)|=(2539805949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4981573163/10000000000 : ℝ)|^19 ≤ (8273594763321/20000000000000 : ℝ)^15
        have hw : |(4981573163/10000000000 : ℝ)|=(4981573163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(197896551/400000000 : ℝ)|^19 ≤ (10252248043467/25000000000000 : ℝ)^15
        have hw : |(197896551/400000000 : ℝ)|=(197896551/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314031_s1_s1_20 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (-115401913/400000000 : ℝ)*x 0 + (5754500793/10000000000 : ℝ)*x 1 + (1913835161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (115401913/400000000 : ℝ)^19 ≤ (20710654382539/100000000000000 : ℝ)^15 := by
    have hnat : (115401913 : ℕ)^19*100000000000000^15 ≤ 20710654382539^15*400000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115401913 400000000 20710654382539 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5754500793/10000000000 : ℝ)^19 ≤ (24830170385923/50000000000000 : ℝ)^15 := by
    have hnat : (5754500793 : ℕ)^19*50000000000000^15 ≤ 24830170385923^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5754500793 10000000000 24830170385923 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1913835161/5000000000 : ℝ)^19 ≤ (14814502416061/50000000000000 : ℝ)^15 := by
    have hnat : (1913835161 : ℕ)^19*50000000000000^15 ≤ 14814502416061^15*5000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1913835161 5000000000 14814502416061 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-115401913/400000000 : ℝ), (5754500793/10000000000 : ℝ), (1913835161/5000000000 : ℝ)] ![(20710654382539/100000000000000 : ℝ), (24830170385923/50000000000000 : ℝ), (14814502416061/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-115401913/400000000 : ℝ)|^19 ≤ (20710654382539/100000000000000 : ℝ)^15
        have hw : |(-115401913/400000000 : ℝ)|=(115401913/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5754500793/10000000000 : ℝ)|^19 ≤ (24830170385923/50000000000000 : ℝ)^15
        have hw : |(5754500793/10000000000 : ℝ)|=(5754500793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1913835161/5000000000 : ℝ)|^19 ≤ (14814502416061/50000000000000 : ℝ)^15
        have hw : |(1913835161/5000000000 : ℝ)|=(1913835161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314031_s1_s1_21 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (6754092517/10000000000 : ℝ)*x 0 + (-21257043/10000000000 : ℝ)*x 1 + (4767451731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6754092517/10000000000 : ℝ)^19 ≤ (15207513663903/25000000000000 : ℝ)^15 := by
    have hnat : (6754092517 : ℕ)^19*25000000000000^15 ≤ 15207513663903^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6754092517 10000000000 15207513663903 25000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (21257043/10000000000 : ℝ)^19 ≤ (5149285333/12500000000000 : ℝ)^15 := by
    have hnat : (21257043 : ℕ)^19*12500000000000^15 ≤ 5149285333^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21257043 10000000000 5149285333 12500000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4767451731/10000000000 : ℝ)^19 ≤ (39128751049559/100000000000000 : ℝ)^15 := by
    have hnat : (4767451731 : ℕ)^19*100000000000000^15 ≤ 39128751049559^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4767451731 10000000000 39128751049559 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6754092517/10000000000 : ℝ), (-21257043/10000000000 : ℝ), (4767451731/10000000000 : ℝ)] ![(15207513663903/25000000000000 : ℝ), (5149285333/12500000000000 : ℝ), (39128751049559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6754092517/10000000000 : ℝ)|^19 ≤ (15207513663903/25000000000000 : ℝ)^15
        have hw : |(6754092517/10000000000 : ℝ)|=(6754092517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-21257043/10000000000 : ℝ)|^19 ≤ (5149285333/12500000000000 : ℝ)^15
        have hw : |(-21257043/10000000000 : ℝ)|=(21257043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4767451731/10000000000 : ℝ)|^19 ≤ (39128751049559/100000000000000 : ℝ)^15
        have hw : |(4767451731/10000000000 : ℝ)|=(4767451731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314031_s1_s1_22 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (123767529/500000000 : ℝ)*x 0 + (655231771/1000000000 : ℝ)*x 1 + (-3284113999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (123767529/500000000 : ℝ)^19 ≤ (8529230371113/50000000000000 : ℝ)^15 := by
    have hnat : (123767529 : ℕ)^19*50000000000000^15 ≤ 8529230371113^15*500000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      123767529 500000000 8529230371113 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655231771/1000000000 : ℝ)^19 ≤ (58537423072507/100000000000000 : ℝ)^15 := by
    have hnat : (655231771 : ℕ)^19*100000000000000^15 ≤ 58537423072507^15*1000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655231771 1000000000 58537423072507 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3284113999/10000000000 : ℝ)^19 ≤ (1525257261029/6250000000000 : ℝ)^15 := by
    have hnat : (3284113999 : ℕ)^19*6250000000000^15 ≤ 1525257261029^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3284113999 10000000000 1525257261029 6250000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(123767529/500000000 : ℝ), (655231771/1000000000 : ℝ), (-3284113999/10000000000 : ℝ)] ![(8529230371113/50000000000000 : ℝ), (58537423072507/100000000000000 : ℝ), (1525257261029/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(123767529/500000000 : ℝ)|^19 ≤ (8529230371113/50000000000000 : ℝ)^15
        have hw : |(123767529/500000000 : ℝ)|=(123767529/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655231771/1000000000 : ℝ)|^19 ≤ (58537423072507/100000000000000 : ℝ)^15
        have hw : |(655231771/1000000000 : ℝ)|=(655231771/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3284113999/10000000000 : ℝ)|^19 ≤ (1525257261029/6250000000000 : ℝ)^15
        have hw : |(-3284113999/10000000000 : ℝ)|=(3284113999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314031_s1_s1_25 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ)) (x : Fin 3 → ℝ) :
    (4837724463/10000000000 : ℝ)*x 0 + (4316282613/10000000000 : ℝ)*x 1 + (3414761909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4837724463/10000000000 : ℝ)^19 ≤ (39860746721001/100000000000000 : ℝ)^15 := by
    have hnat : (4837724463 : ℕ)^19*100000000000000^15 ≤ 39860746721001^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4837724463 10000000000 39860746721001 100000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4316282613/10000000000 : ℝ)^19 ≤ (17249473478209/50000000000000 : ℝ)^15 := by
    have hnat : (4316282613 : ℕ)^19*50000000000000^15 ≤ 17249473478209^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316282613 10000000000 17249473478209 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3414761909/10000000000 : ℝ)^19 ≤ (12820153156309/50000000000000 : ℝ)^15 := by
    have hnat : (3414761909 : ℕ)^19*50000000000000^15 ≤ 12820153156309^15*10000000000^19 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3414761909 10000000000 12820153156309 50000000000000 19 15 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (19/4 : ℝ)) 19 15 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4837724463/10000000000 : ℝ), (4316282613/10000000000 : ℝ), (3414761909/10000000000 : ℝ)] ![(39860746721001/100000000000000 : ℝ), (17249473478209/50000000000000 : ℝ), (12820153156309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4837724463/10000000000 : ℝ)|^19 ≤ (39860746721001/100000000000000 : ℝ)^15
        have hw : |(4837724463/10000000000 : ℝ)|=(4837724463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4316282613/10000000000 : ℝ)|^19 ≤ (17249473478209/50000000000000 : ℝ)^15
        have hw : |(4316282613/10000000000 : ℝ)|=(4316282613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3414761909/10000000000 : ℝ)|^19 ≤ (12820153156309/50000000000000 : ℝ)^15
        have hw : |(3414761909/10000000000 : ℝ)|=(3414761909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314031_s1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((36001/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(36001/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(56771/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(56771/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79153/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(79153/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3201/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3201/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(513/5000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(513/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7389/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7389/20000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (15771/20000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (15771/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (15771/20000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((-1 : ℝ)*(X 0 0+X 2 0)) ∧ ((-1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((-1 : ℝ)*pair X 1 0) ∧ ((-1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15771/20000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
  have base40 : ((-1 : ℝ)*X 1 1+(1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 1+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.2.1]
  have base50 : ((1 : ℝ)*X 0 0+(1 : ℝ)*X 0 2+(1 : ℝ)*X 2 0+(1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
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
  have s1_pow0 : (36001/50000 : ℝ) ^ (37/8 : ℝ) ≤ (21888630498178356193/100000000000000000000 : ℝ) := by
    have hpowers : (36001/50000 : ℝ)^37 ≤ (21888630498178356193/100000000000000000000 : ℝ)^8 := by
      have hnat : (36001 : ℕ)^37*100000000000000000000^8 ≤ 21888630498178356193^8*50000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        36001 50000 21888630498178356193 100000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (36001/50000 : ℝ)) (X := (21888630498178356193/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (121888630498178356193/100000000000000000000 : ℝ) ≤ (5218631623268811/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (121888630498178356193/100000000000000000000 : ℝ)^8 ≤ (5218631623268811/5000000000000000 : ℝ)^37 := by
      have hnat : (121888630498178356193 : ℕ)^8*5000000000000000^37 ≤ 5218631623268811^37*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        121888630498178356193 100000000000000000000 5218631623268811 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5218631623268811/5000000000000000 : ℝ)) (X := (121888630498178356193/100000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (71888630498178356193/50000000000000000000 : ℝ) ≤ (1081670983528997/1000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (71888630498178356193/50000000000000000000 : ℝ)^8 ≤ (1081670983528997/1000000000000000 : ℝ)^37 := by
      have hnat : (71888630498178356193 : ℕ)^8*1000000000000000^37 ≤ 1081670983528997^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        71888630498178356193 50000000000000000000 1081670983528997 1000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1081670983528997/1000000000000000 : ℝ)) (X := (71888630498178356193/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(218631623268811/3600100000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(94861647188087/1800050000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (36001/50000 : ℝ)) (alpha := (218631623268811/3600100000000000 : ℝ)) (beta := (94861647188087/1800050000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (36001/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(218631623268811/3600100000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(94861647188087/1800050000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (56771/100000 : ℝ) ^ (37/8 : ℝ) ≤ (3645904355060919713/50000000000000000000 : ℝ) := by
    have hpowers : (56771/100000 : ℝ)^37 ≤ (3645904355060919713/50000000000000000000 : ℝ)^8 := by
      have hnat : (56771 : ℕ)^37*50000000000000000000^8 ≤ 3645904355060919713^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        56771 100000 3645904355060919713 50000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (56771/100000 : ℝ)) (X := (3645904355060919713/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (53645904355060919713/50000000000000000000 : ℝ) ≤ (10153341354609477/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (53645904355060919713/50000000000000000000 : ℝ)^8 ≤ (10153341354609477/10000000000000000 : ℝ)^37 := by
      have hnat : (53645904355060919713 : ℕ)^8*10000000000000000^37 ≤ 10153341354609477^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        53645904355060919713 50000000000000000000 10153341354609477 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10153341354609477/10000000000000000 : ℝ)) (X := (53645904355060919713/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (28645904355060919713/25000000000000000000 : ℝ) ≤ (1029871996939531/1000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (28645904355060919713/25000000000000000000 : ℝ)^8 ≤ (1029871996939531/1000000000000000 : ℝ)^37 := by
      have hnat : (28645904355060919713 : ℕ)^8*1000000000000000^37 ≤ 1029871996939531^37*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28645904355060919713 25000000000000000000 1029871996939531 1000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1029871996939531/1000000000000000 : ℝ)) (X := (28645904355060919713/25000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(153341354609477/5677100000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 2 0))+(1016633669831/39700000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (56771/100000 : ℝ)) (alpha := (153341354609477/5677100000000000 : ℝ)) (beta := (1016633669831/39700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 1 (by
        change ((-1 : ℝ)*pair X 1 0) ≤ (56771/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(153341354609477/5677100000000000 : ℝ)*((-1 : ℝ)*pair X 1 0)+(1016633669831/39700000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (79153/100000 : ℝ) ^ (37/8 : ℝ) ≤ (33916547064573048083/100000000000000000000 : ℝ) := by
    have hpowers : (79153/100000 : ℝ)^37 ≤ (33916547064573048083/100000000000000000000 : ℝ)^8 := by
      have hnat : (79153 : ℕ)^37*100000000000000000000^8 ≤ 33916547064573048083^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79153 100000 33916547064573048083 100000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (79153/100000 : ℝ)) (X := (33916547064573048083/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (133916547064573048083/100000000000000000000 : ℝ) ≤ (1065181512358903/1000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (133916547064573048083/100000000000000000000 : ℝ)^8 ≤ (1065181512358903/1000000000000000 : ℝ)^37 := by
      have hnat : (133916547064573048083 : ℕ)^8*1000000000000000^37 ≤ 1065181512358903^37*100000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        133916547064573048083 100000000000000000000 1065181512358903 1000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1065181512358903/1000000000000000 : ℝ)) (X := (133916547064573048083/100000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (83916547064573048083/50000000000000000000 : ℝ) ≤ (5592322240821207/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (83916547064573048083/50000000000000000000 : ℝ)^8 ≤ (5592322240821207/5000000000000000 : ℝ)^37 := by
      have hnat : (83916547064573048083 : ℕ)^8*5000000000000000^37 ≤ 5592322240821207^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        83916547064573048083 50000000000000000000 5592322240821207 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5592322240821207/5000000000000000 : ℝ)) (X := (83916547064573048083/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(65181512358903/791530000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(66603669756673/989412500000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (79153/100000 : ℝ)) (alpha := (65181512358903/791530000000000 : ℝ)) (beta := (66603669756673/989412500000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (79153/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(65181512358903/791530000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(66603669756673/989412500000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-416791013/1250000000 : ℝ)*X 0 0+(2742413571/5000000000 : ℝ)*X 0 1+(3700856293/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314031_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((5933064189/10000000000 : ℝ)*X 1 0+(-590335497/10000000000 : ℝ)*X 1 1+(672513843/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314031_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((3088000781/10000000000 : ℝ)*X 2 0+(5937200087/10000000000 : ℝ)*X 2 1+(-3427451279/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314031_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_4 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*P 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314031_s1_s1_4 p hpa hpb (pair X 1)
    change _ ≤ P 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4036839229/10000000000 : ℝ)*X 0 0+(2440107099/5000000000 : ℝ)*X 0 1+(3660611349/10000000000 : ℝ)*X 0 2+(4036839229/10000000000 : ℝ)*X 1 0+(2440107099/5000000000 : ℝ)*X 1 1+(3660611349/10000000000 : ℝ)*X 1 2+(4036839229/10000000000 : ℝ)*X 2 0+(2440107099/5000000000 : ℝ)*X 2 1+(3660611349/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314031_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-13119287/39062500 : ℝ)*X 0 0+(5490460747/10000000000 : ℝ)*X 0 1+(1835499199/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314031_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((2862897889/5000000000 : ℝ)*X 1 0+(-3501311/5000000000 : ℝ)*X 1 1+(1461055751/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314031_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((2749772163/10000000000 : ℝ)*X 2 0+(410410753/625000000 : ℝ)*X 2 1+(-3005596719/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314031_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_12 : ((470974417/1250000000 : ℝ)*X 0 0+(2480452603/5000000000 : ℝ)*X 0 1+(961431259/2500000000 : ℝ)*X 0 2+(470974417/1250000000 : ℝ)*X 1 0+(2480452603/5000000000 : ℝ)*X 1 1+(961431259/2500000000 : ℝ)*X 1 2+(470974417/1250000000 : ℝ)*X 2 0+(2480452603/5000000000 : ℝ)*X 2 1+(961431259/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314031_s1_s1_12 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((-343828481/1000000000 : ℝ)*X 0 0+(458891061/1000000000 : ℝ)*X 0 1+(4547253017/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314031_s1_s1_13 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((3599802731/5000000000 : ℝ)*X 1 0+(-438161831/10000000000 : ℝ)*X 1 1+(4081619601/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314031_s1_s1_14 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((1208919033/5000000000 : ℝ)*X 2 0+(3232667491/5000000000 : ℝ)*X 2 1+(-107521529/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314031_s1_s1_15 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_19 : ((2539805949/10000000000 : ℝ)*X 0 0+(4981573163/10000000000 : ℝ)*X 0 1+(197896551/400000000 : ℝ)*X 0 2+(2539805949/10000000000 : ℝ)*X 1 0+(4981573163/10000000000 : ℝ)*X 1 1+(197896551/400000000 : ℝ)*X 1 2+(2539805949/10000000000 : ℝ)*X 2 0+(4981573163/10000000000 : ℝ)*X 2 1+(197896551/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314031_s1_s1_19 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((-115401913/400000000 : ℝ)*X 0 0+(5754500793/10000000000 : ℝ)*X 0 1+(1913835161/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314031_s1_s1_20 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((6754092517/10000000000 : ℝ)*X 1 0+(-21257043/10000000000 : ℝ)*X 1 1+(4767451731/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314031_s1_s1_21 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((123767529/500000000 : ℝ)*X 2 0+(655231771/1000000000 : ℝ)*X 2 1+(-3284113999/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314031_s1_s1_22 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_25 : ((4837724463/10000000000 : ℝ)*X 0 0+(4316282613/10000000000 : ℝ)*X 0 1+(3414761909/10000000000 : ℝ)*X 0 2+(4837724463/10000000000 : ℝ)*X 1 0+(4316282613/10000000000 : ℝ)*X 1 1+(3414761909/10000000000 : ℝ)*X 1 2+(4837724463/10000000000 : ℝ)*X 2 0+(4316282613/10000000000 : ℝ)*X 2 1+(3414761909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314031_s1_s1_25 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((3201/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3201/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (2369510167649680882478396379/224679748150000000000000000000000 : ℝ) := by norm_num
    linear_combination (1862566131697/1000000000000 : ℝ)*(base50) + (10271/31250000000 : ℝ)*(base60) + (6278668160369/1000000000000 : ℝ)*(major_s1_0) + (1256720438859/125000000000 : ℝ)*(major_s1_1) + (6278668160369/1000000000000 : ℝ)*(major_s1_2) + (438291407/1000000000000 : ℝ)*(sp_s1_0) + (45371749/1000000000000 : ℝ)*(sp_s1_1) + (3775095350503/1000000000000 : ℝ)*(sp_s1_4) + (556743936101/62500000000 : ℝ)*(sp_s1_7) + (4454181390531/500000000000 : ℝ)*(sp_s1_8) + (8908408152811/1000000000000 : ℝ)*(sp_s1_9) + (1824443455243/500000000000 : ℝ)*(sp_s1_12) + (1179439/31250000000 : ℝ)*(sp_s1_19) + (16720947/250000000000 : ℝ)*(sp_s1_20) + (1824462326267/500000000000 : ℝ)*(f.failure) + (8908408152811/1000000000000 : ℝ)*(f.sum) + (13423319379592481849/224679748150000000000000000000000 : ℝ)*base63 + (605597039547649/1978825000000000000000000000 : ℝ)*base65 + (6394987927081/19850000000000000000000000 : ℝ)*base67 + (214712558677739/395765000000000000000000000 : ℝ)*base68 + (148957337941719630133/284958715300000000000000000000000 : ℝ)*base71 + (123912303476897/1800050000000000000000000000 : ℝ)*base72 + (627948618359973/2838550000000000000000000000 : ℝ)*base75 + (200958329277421/3600100000000000000000000000 : ℝ)*base76 + (91178959201369003/178654962500000000000000000000 : ℝ)*base79 + (13577/50000000000000000 : ℝ)*base86 + (13577/50000000000000000 : ℝ)*base88 + (13577/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(513/5000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(513/5000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (332085332368546007818170987/22467974815000000000000000000000 : ℝ) := by norm_num
    linear_combination (69653/50000000000 : ℝ)*(base24) + (477771683769/1000000000000 : ℝ)*(base40) + (238561614721/1000000000000 : ℝ)*(base50) + (44557507349/200000000000 : ℝ)*(base60) + (513574345341/200000000000 : ℝ)*(major_s1_0) + (513574345341/200000000000 : ℝ)*(major_s1_1) + (513574345341/200000000000 : ℝ)*(major_s1_2) + (158788689/1000000000000 : ℝ)*(sp_s1_2) + (910846002273/250000000000 : ℝ)*(sp_s1_13) + (1821653607793/500000000000 : ℝ)*(sp_s1_14) + (910807085459/250000000000 : ℝ)*(sp_s1_15) + (59694000121/40000000000 : ℝ)*(sp_s1_19) + (4514493/1000000000000 : ℝ)*(sp_s1_20) + (40653999/500000000000 : ℝ)*(sp_s1_21) + (59694000121/40000000000 : ℝ)*(f.failure) + (728677704717/200000000000 : ℝ)*(f.sum) + (9135296701938809671/89871899260000000000000000000000 : ℝ)*base62 + (11543746691853/39576500000000000000000000 : ℝ)*base64 + (3861869780519/7940000000000000000000000 : ℝ)*base66 + (100438241755237/98941250000000000000000000 : ℝ)*base69 + (8117379355339021423/56991743060000000000000000000000 : ℝ)*base70 + (293387653803/1406289062500000000000000 : ℝ)*base73 + (567162022854077/1135420000000000000000000000 : ℝ)*base74 + (32140440337611/720020000000000000000000000 : ℝ)*base77 + (51942939273009163/57169588000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base82 + (349/4000000000000000 : ℝ)*base87 + (349/4000000000000000 : ℝ)*base89 + (349/4000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7389/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7389/20000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (35270341476735604650339114584319/2022173903287037500000000000000000000 : ℝ) := by norm_num
    linear_combination (381242663689/500000000000 : ℝ)*(base40) + (1793807034007/1000000000000 : ℝ)*(base50) + (3182746723627/500000000000 : ℝ)*(major_s1_0) + (10114344845661/500000000000 : ℝ)*(major_s1_1) + (3182746723627/500000000000 : ℝ)*(major_s1_2) + (7933877/500000000000 : ℝ)*(sp_s1_2) + (3465799061017/250000000000 : ℝ)*(sp_s1_4) + (62564723/1000000000000 : ℝ)*(sp_s1_6) + (45622123/200000000000 : ℝ)*(sp_s1_9) + (52829933/500000000000 : ℝ)*(sp_s1_14) + (9031596852583/1000000000000 : ℝ)*(sp_s1_20) + (9031491192717/1000000000000 : ℝ)*(sp_s1_21) + (9031352874213/1000000000000 : ℝ)*(sp_s1_22) + (115603801977/31250000000 : ℝ)*(sp_s1_25) + (1849692113993/500000000000 : ℝ)*(f.failure) + (9031596852583/1000000000000 : ℝ)*(f.sum) + (3701030086502727509/224679748150000000000000000000000 : ℝ)*base63 + (1184376966064557/3957650000000000000000000000 : ℝ)*base64 + (385450402863/9925000000000000000000000 : ℝ)*base67 + (134007160251189/395765000000000000000000000 : ℝ)*base68 + (9642599499384218447/17809919706250000000000000000000 : ℝ)*base70 + (81005291369309/900025000000000000000000000 : ℝ)*base73 + (688722795490113/2838550000000000000000000000 : ℝ)*base75 + (43086399965827/1800050000000000000000000000 : ℝ)*base77 + (8170828287134209/89327481250000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (38483/50000000000000000 : ℝ)*base86 + (38483/50000000000000000 : ℝ)*base88 + (38483/50000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (19/4 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![false, true, true], ![true, true, true]])
    (hprev0 : (0 : ℝ) ≤ ((36001/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(36001/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(56771/100000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(56771/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(79153/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(79153/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3201/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3201/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(513/5000 : ℝ)*X 0 1+(1 : ℝ)*X 2 0+(513/5000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(7389/20000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(7389/20000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c314031_s1 p hpa hpb X hX hprev0

#print axioms solution
