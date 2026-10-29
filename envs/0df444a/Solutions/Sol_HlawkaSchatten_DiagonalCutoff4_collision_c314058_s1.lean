-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c314058_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:47:40.260312+00:00
-- url     : https://prove2.me/submissions/f262bbbe-3698-4703-ae3c-84f298412687

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
theorem collision_support_c314058_s1_s1_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-844547161/2500000000 : ℝ)*x 0 + (3310885283/10000000000 : ℝ)*x 1 + (-2911958447/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (844547161/2500000000 : ℝ)^75 ≤ (25169197084231/100000000000000 : ℝ)^59 := by
    have hnat : (844547161 : ℕ)^75*100000000000000^59 ≤ 25169197084231^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      844547161 2500000000 25169197084231 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3310885283/10000000000 : ℝ)^75 ≤ (24533498961519/100000000000000 : ℝ)^59 := by
    have hnat : (3310885283 : ℕ)^75*100000000000000^59 ≤ 24533498961519^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3310885283 10000000000 24533498961519 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2911958447/5000000000 : ℝ)^75 ≤ (50297303941861/100000000000000 : ℝ)^59 := by
    have hnat : (2911958447 : ℕ)^75*100000000000000^59 ≤ 50297303941861^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2911958447 5000000000 50297303941861 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-844547161/2500000000 : ℝ), (3310885283/10000000000 : ℝ), (-2911958447/5000000000 : ℝ)] ![(25169197084231/100000000000000 : ℝ), (24533498961519/100000000000000 : ℝ), (50297303941861/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-844547161/2500000000 : ℝ)|^75 ≤ (25169197084231/100000000000000 : ℝ)^59
        have hw : |(-844547161/2500000000 : ℝ)|=(844547161/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3310885283/10000000000 : ℝ)|^75 ≤ (24533498961519/100000000000000 : ℝ)^59
        have hw : |(3310885283/10000000000 : ℝ)|=(3310885283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2911958447/5000000000 : ℝ)|^75 ≤ (50297303941861/100000000000000 : ℝ)^59
        have hw : |(-2911958447/5000000000 : ℝ)|=(2911958447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314058_s1_s1_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1560688329/5000000000 : ℝ)*x 0 + (-1526181473/5000000000 : ℝ)*x 1 + (-6258241381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1560688329/5000000000 : ℝ)^75 ≤ (22762487391449/100000000000000 : ℝ)^59 := by
    have hnat : (1560688329 : ℕ)^75*100000000000000^59 ≤ 22762487391449^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1560688329 5000000000 22762487391449 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1526181473/5000000000 : ℝ)^75 ≤ (22124654164749/100000000000000 : ℝ)^59 := by
    have hnat : (1526181473 : ℕ)^75*100000000000000^59 ≤ 22124654164749^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1526181473 5000000000 22124654164749 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6258241381/10000000000 : ℝ)^75 ≤ (55112858433459/100000000000000 : ℝ)^59 := by
    have hnat : (6258241381 : ℕ)^75*100000000000000^59 ≤ 55112858433459^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6258241381 10000000000 55112858433459 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1560688329/5000000000 : ℝ), (-1526181473/5000000000 : ℝ), (-6258241381/10000000000 : ℝ)] ![(22762487391449/100000000000000 : ℝ), (22124654164749/100000000000000 : ℝ), (55112858433459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1560688329/5000000000 : ℝ)|^75 ≤ (22762487391449/100000000000000 : ℝ)^59
        have hw : |(1560688329/5000000000 : ℝ)|=(1560688329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1526181473/5000000000 : ℝ)|^75 ≤ (22124654164749/100000000000000 : ℝ)^59
        have hw : |(-1526181473/5000000000 : ℝ)|=(1526181473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6258241381/10000000000 : ℝ)|^75 ≤ (55112858433459/100000000000000 : ℝ)^59
        have hw : |(-6258241381/10000000000 : ℝ)|=(6258241381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314058_s1_s1_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (345983109/625000000 : ℝ)*x 0 + (5268026701/10000000000 : ℝ)*x 1 + (723713169/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (345983109/625000000 : ℝ)^75 ≤ (23577480461589/50000000000000 : ℝ)^59 := by
    have hnat : (345983109 : ℕ)^75*50000000000000^59 ≤ 23577480461589^59*625000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345983109 625000000 23577480461589 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5268026701/10000000000 : ℝ)^75 ≤ (22137709028483/50000000000000 : ℝ)^59 := by
    have hnat : (5268026701 : ℕ)^75*50000000000000^59 ≤ 22137709028483^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5268026701 10000000000 22137709028483 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (723713169/5000000000 : ℝ)^75 ≤ (2142405251979/25000000000000 : ℝ)^59 := by
    have hnat : (723713169 : ℕ)^75*25000000000000^59 ≤ 2142405251979^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      723713169 5000000000 2142405251979 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(345983109/625000000 : ℝ), (5268026701/10000000000 : ℝ), (723713169/5000000000 : ℝ)] ![(23577480461589/50000000000000 : ℝ), (22137709028483/50000000000000 : ℝ), (2142405251979/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(345983109/625000000 : ℝ)|^75 ≤ (23577480461589/50000000000000 : ℝ)^59
        have hw : |(345983109/625000000 : ℝ)|=(345983109/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5268026701/10000000000 : ℝ)|^75 ≤ (22137709028483/50000000000000 : ℝ)^59
        have hw : |(5268026701/10000000000 : ℝ)|=(5268026701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(723713169/5000000000 : ℝ)|^75 ≤ (2142405251979/25000000000000 : ℝ)^59
        have hw : |(723713169/5000000000 : ℝ)|=(723713169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314058_s1_s1_6 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4410709889/10000000000 : ℝ)*x 0 + (261738807/400000000 : ℝ)*x 1 + (-571523901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4410709889/10000000000 : ℝ)^75 ≤ (17663388503893/50000000000000 : ℝ)^59 := by
    have hnat : (4410709889 : ℕ)^75*50000000000000^59 ≤ 17663388503893^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4410709889 10000000000 17663388503893 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261738807/400000000 : ℝ)^75 ≤ (58325408457393/100000000000000 : ℝ)^59 := by
    have hnat : (261738807 : ℕ)^75*100000000000000^59 ≤ 58325408457393^59*400000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261738807 400000000 58325408457393 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (571523901/5000000000 : ℝ)^75 ≤ (793476814687/12500000000000 : ℝ)^59 := by
    have hnat : (571523901 : ℕ)^75*12500000000000^59 ≤ 793476814687^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571523901 5000000000 793476814687 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4410709889/10000000000 : ℝ), (261738807/400000000 : ℝ), (-571523901/5000000000 : ℝ)] ![(17663388503893/50000000000000 : ℝ), (58325408457393/100000000000000 : ℝ), (793476814687/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4410709889/10000000000 : ℝ)|^75 ≤ (17663388503893/50000000000000 : ℝ)^59
        have hw : |(4410709889/10000000000 : ℝ)|=(4410709889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(261738807/400000000 : ℝ)|^75 ≤ (58325408457393/100000000000000 : ℝ)^59
        have hw : |(261738807/400000000 : ℝ)|=(261738807/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-571523901/5000000000 : ℝ)|^75 ≤ (793476814687/12500000000000 : ℝ)^59
        have hw : |(-571523901/5000000000 : ℝ)|=(571523901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314058_s1_s1_7 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-384212051/1250000000 : ℝ)*x 0 + (707321369/2500000000 : ℝ)*x 1 + (-323917911/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (384212051/1250000000 : ℝ)^75 ≤ (22321407268033/100000000000000 : ℝ)^59 := by
    have hnat : (384212051 : ℕ)^75*100000000000000^59 ≤ 22321407268033^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      384212051 1250000000 22321407268033 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (707321369/2500000000 : ℝ)^75 ≤ (20089954127693/100000000000000 : ℝ)^59 := by
    have hnat : (707321369 : ℕ)^75*100000000000000^59 ≤ 20089954127693^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      707321369 2500000000 20089954127693 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323917911/500000000 : ℝ)^75 ≤ (28794319292063/50000000000000 : ℝ)^59 := by
    have hnat : (323917911 : ℕ)^75*50000000000000^59 ≤ 28794319292063^59*500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323917911 500000000 28794319292063 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-384212051/1250000000 : ℝ), (707321369/2500000000 : ℝ), (-323917911/500000000 : ℝ)] ![(22321407268033/100000000000000 : ℝ), (20089954127693/100000000000000 : ℝ), (28794319292063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-384212051/1250000000 : ℝ)|^75 ≤ (22321407268033/100000000000000 : ℝ)^59
        have hw : |(-384212051/1250000000 : ℝ)|=(384212051/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(707321369/2500000000 : ℝ)|^75 ≤ (20089954127693/100000000000000 : ℝ)^59
        have hw : |(707321369/2500000000 : ℝ)|=(707321369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-323917911/500000000 : ℝ)|^75 ≤ (28794319292063/50000000000000 : ℝ)^59
        have hw : |(-323917911/500000000 : ℝ)|=(323917911/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314058_s1_s1_8 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3152082233/10000000000 : ℝ)*x 0 + (-1427428311/5000000000 : ℝ)*x 1 + (-6393499793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3152082233/10000000000 : ℝ)^75 ≤ (2304750884453/10000000000000 : ℝ)^59 := by
    have hnat : (3152082233 : ℕ)^75*10000000000000^59 ≤ 2304750884453^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3152082233 10000000000 2304750884453 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1427428311/5000000000 : ℝ)^75 ≤ (20321050088957/100000000000000 : ℝ)^59 := by
    have hnat : (1427428311 : ℕ)^75*100000000000000^59 ≤ 20321050088957^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1427428311 5000000000 20321050088957 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6393499793/10000000000 : ℝ)^75 ≤ (56631441048601/100000000000000 : ℝ)^59 := by
    have hnat : (6393499793 : ℕ)^75*100000000000000^59 ≤ 56631441048601^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6393499793 10000000000 56631441048601 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3152082233/10000000000 : ℝ), (-1427428311/5000000000 : ℝ), (-6393499793/10000000000 : ℝ)] ![(2304750884453/10000000000000 : ℝ), (20321050088957/100000000000000 : ℝ), (56631441048601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3152082233/10000000000 : ℝ)|^75 ≤ (2304750884453/10000000000000 : ℝ)^59
        have hw : |(3152082233/10000000000 : ℝ)|=(3152082233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1427428311/5000000000 : ℝ)|^75 ≤ (20321050088957/100000000000000 : ℝ)^59
        have hw : |(-1427428311/5000000000 : ℝ)|=(1427428311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6393499793/10000000000 : ℝ)|^75 ≤ (56631441048601/100000000000000 : ℝ)^59
        have hw : |(-6393499793/10000000000 : ℝ)|=(6393499793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314058_s1_s1_9 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (698748787/1250000000 : ℝ)*x 0 + (2727270407/5000000000 : ℝ)*x 1 + (272622773/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (698748787/1250000000 : ℝ)^75 ≤ (4774329150783/10000000000000 : ℝ)^59 := by
    have hnat : (698748787 : ℕ)^75*10000000000000^59 ≤ 4774329150783^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      698748787 1250000000 4774329150783 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2727270407/5000000000 : ℝ)^75 ≤ (2892348400733/6250000000000 : ℝ)^59 := by
    have hnat : (2727270407 : ℕ)^75*6250000000000^59 ≤ 2892348400733^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2727270407 5000000000 2892348400733 6250000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272622773/2500000000 : ℝ)^75 ≤ (5979134060507/100000000000000 : ℝ)^59 := by
    have hnat : (272622773 : ℕ)^75*100000000000000^59 ≤ 5979134060507^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272622773 2500000000 5979134060507 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(698748787/1250000000 : ℝ), (2727270407/5000000000 : ℝ), (272622773/2500000000 : ℝ)] ![(4774329150783/10000000000000 : ℝ), (2892348400733/6250000000000 : ℝ), (5979134060507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(698748787/1250000000 : ℝ)|^75 ≤ (4774329150783/10000000000000 : ℝ)^59
        have hw : |(698748787/1250000000 : ℝ)|=(698748787/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2727270407/5000000000 : ℝ)|^75 ≤ (2892348400733/6250000000000 : ℝ)^59
        have hw : |(2727270407/5000000000 : ℝ)|=(2727270407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(272622773/2500000000 : ℝ)|^75 ≤ (5979134060507/100000000000000 : ℝ)^59
        have hw : |(272622773/2500000000 : ℝ)|=(272622773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314058_s1_s1_13 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4119848079/10000000000 : ℝ)*x 0 + (181083989/250000000 : ℝ)*x 1 + (-79077187/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4119848079/10000000000 : ℝ)^75 ≤ (16196165639979/50000000000000 : ℝ)^59 := by
    have hnat : (4119848079 : ℕ)^75*50000000000000^59 ≤ 16196165639979^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4119848079 10000000000 16196165639979 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (181083989/250000000 : ℝ)^75 ≤ (33183919984197/50000000000000 : ℝ)^59 := by
    have hnat : (181083989 : ℕ)^75*50000000000000^59 ≤ 33183919984197^59*250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181083989 250000000 33183919984197 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79077187/2500000000 : ℝ)^75 ≤ (619914369401/50000000000000 : ℝ)^59 := by
    have hnat : (79077187 : ℕ)^75*50000000000000^59 ≤ 619914369401^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79077187 2500000000 619914369401 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4119848079/10000000000 : ℝ), (181083989/250000000 : ℝ), (-79077187/2500000000 : ℝ)] ![(16196165639979/50000000000000 : ℝ), (33183919984197/50000000000000 : ℝ), (619914369401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4119848079/10000000000 : ℝ)|^75 ≤ (16196165639979/50000000000000 : ℝ)^59
        have hw : |(4119848079/10000000000 : ℝ)|=(4119848079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(181083989/250000000 : ℝ)|^75 ≤ (33183919984197/50000000000000 : ℝ)^59
        have hw : |(181083989/250000000 : ℝ)|=(181083989/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-79077187/2500000000 : ℝ)|^75 ≤ (619914369401/50000000000000 : ℝ)^59
        have hw : |(-79077187/2500000000 : ℝ)|=(79077187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314058_s1_s1_14 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-2888249753/10000000000 : ℝ)*x 0 + (610695443/2000000000 : ℝ)*x 1 + (-644760921/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2888249753/10000000000 : ℝ)^75 ≤ (5155920470431/25000000000000 : ℝ)^59 := by
    have hnat : (2888249753 : ℕ)^75*25000000000000^59 ≤ 5155920470431^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2888249753 10000000000 5155920470431 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (610695443/2000000000 : ℝ)^75 ≤ (11067460789831/50000000000000 : ℝ)^59 := by
    have hnat : (610695443 : ℕ)^75*50000000000000^59 ≤ 11067460789831^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      610695443 2000000000 11067460789831 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (644760921/1000000000 : ℝ)^75 ≤ (2862069826157/5000000000000 : ℝ)^59 := by
    have hnat : (644760921 : ℕ)^75*5000000000000^59 ≤ 2862069826157^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      644760921 1000000000 2862069826157 5000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2888249753/10000000000 : ℝ), (610695443/2000000000 : ℝ), (-644760921/1000000000 : ℝ)] ![(5155920470431/25000000000000 : ℝ), (11067460789831/50000000000000 : ℝ), (2862069826157/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2888249753/10000000000 : ℝ)|^75 ≤ (5155920470431/25000000000000 : ℝ)^59
        have hw : |(-2888249753/10000000000 : ℝ)|=(2888249753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(610695443/2000000000 : ℝ)|^75 ≤ (11067460789831/50000000000000 : ℝ)^59
        have hw : |(610695443/2000000000 : ℝ)|=(610695443/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-644760921/1000000000 : ℝ)|^75 ≤ (2862069826157/5000000000000 : ℝ)^59
        have hw : |(-644760921/1000000000 : ℝ)|=(644760921/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314058_s1_s1_15 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1423201157/5000000000 : ℝ)*x 0 + (-608123919/2000000000 : ℝ)*x 1 + (-6491652789/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1423201157/5000000000 : ℝ)^75 ≤ (4048916598021/20000000000000 : ℝ)^59 := by
    have hnat : (1423201157 : ℕ)^75*20000000000000^59 ≤ 4048916598021^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1423201157 5000000000 4048916598021 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (608123919/2000000000 : ℝ)^75 ≤ (5504126772117/25000000000000 : ℝ)^59 := by
    have hnat : (608123919 : ℕ)^75*25000000000000^59 ≤ 5504126772117^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      608123919 2000000000 5504126772117 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6491652789/10000000000 : ℝ)^75 ≤ (3608681869761/6250000000000 : ℝ)^59 := by
    have hnat : (6491652789 : ℕ)^75*6250000000000^59 ≤ 3608681869761^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6491652789 10000000000 3608681869761 6250000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1423201157/5000000000 : ℝ), (-608123919/2000000000 : ℝ), (-6491652789/10000000000 : ℝ)] ![(4048916598021/20000000000000 : ℝ), (5504126772117/25000000000000 : ℝ), (3608681869761/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1423201157/5000000000 : ℝ)|^75 ≤ (4048916598021/20000000000000 : ℝ)^59
        have hw : |(1423201157/5000000000 : ℝ)|=(1423201157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-608123919/2000000000 : ℝ)|^75 ≤ (5504126772117/25000000000000 : ℝ)^59
        have hw : |(-608123919/2000000000 : ℝ)|=(608123919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6491652789/10000000000 : ℝ)|^75 ≤ (3608681869761/6250000000000 : ℝ)^59
        have hw : |(-6491652789/10000000000 : ℝ)|=(6491652789/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314058_s1_s1_16 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1200233707/2000000000 : ℝ)*x 0 + (5192239319/10000000000 : ℝ)*x 1 + (209633313/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1200233707/2000000000 : ℝ)^75 ≤ (26125607035293/50000000000000 : ℝ)^59 := by
    have hnat : (1200233707 : ℕ)^75*50000000000000^59 ≤ 26125607035293^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1200233707 2000000000 26125607035293 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5192239319/10000000000 : ℝ)^75 ≤ (8693461836547/20000000000000 : ℝ)^59 := by
    have hnat : (5192239319 : ℕ)^75*20000000000000^59 ≤ 8693461836547^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5192239319 10000000000 8693461836547 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209633313/2500000000 : ℝ)^75 ≤ (4281476730257/100000000000000 : ℝ)^59 := by
    have hnat : (209633313 : ℕ)^75*100000000000000^59 ≤ 4281476730257^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209633313 2500000000 4281476730257 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1200233707/2000000000 : ℝ), (5192239319/10000000000 : ℝ), (209633313/2500000000 : ℝ)] ![(26125607035293/50000000000000 : ℝ), (8693461836547/20000000000000 : ℝ), (4281476730257/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1200233707/2000000000 : ℝ)|^75 ≤ (26125607035293/50000000000000 : ℝ)^59
        have hw : |(1200233707/2000000000 : ℝ)|=(1200233707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5192239319/10000000000 : ℝ)|^75 ≤ (8693461836547/20000000000000 : ℝ)^59
        have hw : |(5192239319/10000000000 : ℝ)|=(5192239319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209633313/2500000000 : ℝ)|^75 ≤ (4281476730257/100000000000000 : ℝ)^59
        have hw : |(209633313/2500000000 : ℝ)|=(209633313/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314058_s1_s1_20 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (225358421/500000000 : ℝ)*x 0 + (3420952199/5000000000 : ℝ)*x 1 + (-226809759/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (225358421/500000000 : ℝ)^75 ≤ (18155875284329/50000000000000 : ℝ)^59 := by
    have hnat : (225358421 : ℕ)^75*50000000000000^59 ≤ 18155875284329^59*500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225358421 500000000 18155875284329 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3420952199/5000000000 : ℝ)^75 ≤ (30863789160513/50000000000000 : ℝ)^59 := by
    have hnat : (3420952199 : ℕ)^75*50000000000000^59 ≤ 30863789160513^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3420952199 5000000000 30863789160513 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (226809759/5000000000 : ℝ)^75 ≤ (1960671089233/100000000000000 : ℝ)^59 := by
    have hnat : (226809759 : ℕ)^75*100000000000000^59 ≤ 1960671089233^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226809759 5000000000 1960671089233 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(225358421/500000000 : ℝ), (3420952199/5000000000 : ℝ), (-226809759/5000000000 : ℝ)] ![(18155875284329/50000000000000 : ℝ), (30863789160513/50000000000000 : ℝ), (1960671089233/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(225358421/500000000 : ℝ)|^75 ≤ (18155875284329/50000000000000 : ℝ)^59
        have hw : |(225358421/500000000 : ℝ)|=(225358421/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3420952199/5000000000 : ℝ)|^75 ≤ (30863789160513/50000000000000 : ℝ)^59
        have hw : |(3420952199/5000000000 : ℝ)|=(3420952199/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-226809759/5000000000 : ℝ)|^75 ≤ (1960671089233/100000000000000 : ℝ)^59
        have hw : |(-226809759/5000000000 : ℝ)|=(226809759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314058_s1_s1_21 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-3324445119/10000000000 : ℝ)*x 0 + (816318109/2500000000 : ℝ)*x 1 + (-5909074711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3324445119/10000000000 : ℝ)^75 ≤ (24661295742809/100000000000000 : ℝ)^59 := by
    have hnat : (3324445119 : ℕ)^75*100000000000000^59 ≤ 24661295742809^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3324445119 10000000000 24661295742809 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (816318109/2500000000 : ℝ)^75 ≤ (12052328622793/50000000000000 : ℝ)^59 := by
    have hnat : (816318109 : ℕ)^75*50000000000000^59 ≤ 12052328622793^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      816318109 2500000000 12052328622793 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5909074711/10000000000 : ℝ)^75 ≤ (25617023495813/50000000000000 : ℝ)^59 := by
    have hnat : (5909074711 : ℕ)^75*50000000000000^59 ≤ 25617023495813^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5909074711 10000000000 25617023495813 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-3324445119/10000000000 : ℝ), (816318109/2500000000 : ℝ), (-5909074711/10000000000 : ℝ)] ![(24661295742809/100000000000000 : ℝ), (12052328622793/50000000000000 : ℝ), (25617023495813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-3324445119/10000000000 : ℝ)|^75 ≤ (24661295742809/100000000000000 : ℝ)^59
        have hw : |(-3324445119/10000000000 : ℝ)|=(3324445119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(816318109/2500000000 : ℝ)|^75 ≤ (12052328622793/50000000000000 : ℝ)^59
        have hw : |(816318109/2500000000 : ℝ)|=(816318109/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5909074711/10000000000 : ℝ)|^75 ≤ (25617023495813/50000000000000 : ℝ)^59
        have hw : |(-5909074711/10000000000 : ℝ)|=(5909074711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314058_s1_s1_22 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (638758783/2000000000 : ℝ)*x 0 + (-623250993/2000000000 : ℝ)*x 1 + (-6145071237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (638758783/2000000000 : ℝ)^75 ≤ (2929487516739/12500000000000 : ℝ)^59 := by
    have hnat : (638758783 : ℕ)^75*12500000000000^59 ≤ 2929487516739^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      638758783 2000000000 2929487516739 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (623250993/2000000000 : ℝ)^75 ≤ (22715019530649/100000000000000 : ℝ)^59 := by
    have hnat : (623250993 : ℕ)^75*100000000000000^59 ≤ 22715019530649^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      623250993 2000000000 22715019530649 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6145071237/10000000000 : ℝ)^75 ≤ (26924540160653/50000000000000 : ℝ)^59 := by
    have hnat : (6145071237 : ℕ)^75*50000000000000^59 ≤ 26924540160653^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6145071237 10000000000 26924540160653 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(638758783/2000000000 : ℝ), (-623250993/2000000000 : ℝ), (-6145071237/10000000000 : ℝ)] ![(2929487516739/12500000000000 : ℝ), (22715019530649/100000000000000 : ℝ), (26924540160653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(638758783/2000000000 : ℝ)|^75 ≤ (2929487516739/12500000000000 : ℝ)^59
        have hw : |(638758783/2000000000 : ℝ)|=(638758783/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-623250993/2000000000 : ℝ)|^75 ≤ (22715019530649/100000000000000 : ℝ)^59
        have hw : |(-623250993/2000000000 : ℝ)|=(623250993/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-6145071237/10000000000 : ℝ)|^75 ≤ (26924540160653/50000000000000 : ℝ)^59
        have hw : |(-6145071237/10000000000 : ℝ)|=(6145071237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314058_s1_s1_23 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3119541739/5000000000 : ℝ)*x 0 + (1123591243/2500000000 : ℝ)*x 1 + (298778399/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3119541739/5000000000 : ℝ)^75 ≤ (54898481818653/100000000000000 : ℝ)^59 := by
    have hnat : (3119541739 : ℕ)^75*100000000000000^59 ≤ 54898481818653^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3119541739 5000000000 54898481818653 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1123591243/2500000000 : ℝ)^75 ≤ (36180677892971/100000000000000 : ℝ)^59 := by
    have hnat : (1123591243 : ℕ)^75*100000000000000^59 ≤ 36180677892971^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123591243 2500000000 36180677892971 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (298778399/2000000000 : ℝ)^75 ≤ (8920840261147/100000000000000 : ℝ)^59 := by
    have hnat : (298778399 : ℕ)^75*100000000000000^59 ≤ 8920840261147^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      298778399 2000000000 8920840261147 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3119541739/5000000000 : ℝ), (1123591243/2500000000 : ℝ), (298778399/2000000000 : ℝ)] ![(54898481818653/100000000000000 : ℝ), (36180677892971/100000000000000 : ℝ), (8920840261147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3119541739/5000000000 : ℝ)|^75 ≤ (54898481818653/100000000000000 : ℝ)^59
        have hw : |(3119541739/5000000000 : ℝ)|=(3119541739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1123591243/2500000000 : ℝ)|^75 ≤ (36180677892971/100000000000000 : ℝ)^59
        have hw : |(1123591243/2500000000 : ℝ)|=(1123591243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(298778399/2000000000 : ℝ)|^75 ≤ (8920840261147/100000000000000 : ℝ)^59
        have hw : |(298778399/2000000000 : ℝ)|=(298778399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314058_s1_s1_27 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (13073323/40000000 : ℝ)*x 0 + (1965403021/2500000000 : ℝ)*x 1 + (-1951167/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13073323/40000000 : ℝ)^75 ≤ (24133360292559/100000000000000 : ℝ)^59 := by
    have hnat : (13073323 : ℕ)^75*100000000000000^59 ≤ 24133360292559^59*40000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13073323 40000000 24133360292559 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1965403021/2500000000 : ℝ)^75 ≤ (73650512997603/100000000000000 : ℝ)^59 := by
    have hnat : (1965403021 : ℕ)^75*100000000000000^59 ≤ 73650512997603^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1965403021 2500000000 73650512997603 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1951167/39062500 : ℝ)^75 ≤ (554031674493/25000000000000 : ℝ)^59 := by
    have hnat : (1951167 : ℕ)^75*25000000000000^59 ≤ 554031674493^59*39062500^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1951167 39062500 554031674493 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(13073323/40000000 : ℝ), (1965403021/2500000000 : ℝ), (-1951167/39062500 : ℝ)] ![(24133360292559/100000000000000 : ℝ), (73650512997603/100000000000000 : ℝ), (554031674493/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(13073323/40000000 : ℝ)|^75 ≤ (24133360292559/100000000000000 : ℝ)^59
        have hw : |(13073323/40000000 : ℝ)|=(13073323/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1965403021/2500000000 : ℝ)|^75 ≤ (73650512997603/100000000000000 : ℝ)^59
        have hw : |(1965403021/2500000000 : ℝ)|=(1965403021/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1951167/39062500 : ℝ)|^75 ≤ (554031674493/25000000000000 : ℝ)^59
        have hw : |(-1951167/39062500 : ℝ)|=(1951167/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314058_s1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((5173/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5173/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76903/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(76903/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-33633/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-33633/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((41937/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(41937/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18341/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18341/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-6577/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-6577/50000 : ℝ)*X 1 2) := by
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
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (15771/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (15771/20000 : ℝ)*P 2 ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((-1 : ℝ)*(X 0 0+X 1 0)) ∧ ((-1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((-1 : ℝ)*pair X 2 0) ∧ ((-1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base5 : ((1 : ℝ)*N 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [f.Ntotal 2]
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base49 : ((-1 : ℝ)*X 0 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order1.1]
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
  rcases hprev0 with ⟨ratio_s0_0,ratio_s0_1,ratio_s0_2⟩
  have s1_pow0 : (5173/6250 : ℝ) ^ (37/8 : ℝ) ≤ (20848935547546180087/50000000000000000000 : ℝ) := by
    have hpowers : (5173/6250 : ℝ)^37 ≤ (20848935547546180087/50000000000000000000 : ℝ)^8 := by
      have hnat : (5173 : ℕ)^37*50000000000000000000^8 ≤ 20848935547546180087^8*6250^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5173 6250 20848935547546180087 50000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5173/6250 : ℝ)) (X := (20848935547546180087/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (70848935547546180087/50000000000000000000 : ℝ) ≤ (10782692134303661/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (70848935547546180087/50000000000000000000 : ℝ)^8 ≤ (10782692134303661/10000000000000000 : ℝ)^37 := by
      have hnat : (70848935547546180087 : ℕ)^8*10000000000000000^37 ≤ 10782692134303661^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70848935547546180087 50000000000000000000 10782692134303661 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10782692134303661/10000000000000000 : ℝ)) (X := (70848935547546180087/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (45848935547546180087/25000000000000000000 : ℝ) ≤ (1425144954970647/1250000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (45848935547546180087/25000000000000000000 : ℝ)^8 ≤ (1425144954970647/1250000000000000 : ℝ)^37 := by
      have hnat : (45848935547546180087 : ℕ)^8*1250000000000000^37 ≤ 1425144954970647^37*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        45848935547546180087 25000000000000000000 1425144954970647 1250000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1425144954970647/1250000000000000 : ℝ)) (X := (45848935547546180087/25000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(782692134303661/8276800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(123693501092303/1655360000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (5173/6250 : ℝ)) (alpha := (782692134303661/8276800000000000 : ℝ)) (beta := (123693501092303/1655360000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (5173/6250 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(782692134303661/8276800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(123693501092303/1655360000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (76903/100000 : ℝ) ^ (37/8 : ℝ) ≤ (14840812689879982613/50000000000000000000 : ℝ) := by
    have hpowers : (76903/100000 : ℝ)^37 ≤ (14840812689879982613/50000000000000000000 : ℝ)^8 := by
      have hnat : (76903 : ℕ)^37*50000000000000000000^8 ≤ 14840812689879982613^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        76903 100000 14840812689879982613 50000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (76903/100000 : ℝ)) (X := (14840812689879982613/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (64840812689879982613/50000000000000000000 : ℝ) ≤ (10578063026208777/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (64840812689879982613/50000000000000000000 : ℝ)^8 ≤ (10578063026208777/10000000000000000 : ℝ)^37 := by
      have hnat : (64840812689879982613 : ℕ)^8*10000000000000000^37 ≤ 10578063026208777^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        64840812689879982613 50000000000000000000 10578063026208777 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10578063026208777/10000000000000000 : ℝ)) (X := (64840812689879982613/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (39840812689879982613/25000000000000000000 : ℝ) ≤ (11060114079154069/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (39840812689879982613/25000000000000000000 : ℝ)^8 ≤ (11060114079154069/10000000000000000 : ℝ)^37 := by
      have hnat : (39840812689879982613 : ℕ)^8*10000000000000000^37 ≤ 11060114079154069^37*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39840812689879982613 25000000000000000000 11060114079154069 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11060114079154069/10000000000000000 : ℝ)) (X := (39840812689879982613/25000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(10906849551109/145100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(120512763236323/1922575000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (76903/100000 : ℝ)) (alpha := (10906849551109/145100000000000 : ℝ)) (beta := (120512763236323/1922575000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (76903/100000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(10906849551109/145100000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(120512763236323/1922575000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (33633/50000 : ℝ) ^ (37/8 : ℝ) ≤ (7989593213909698551/50000000000000000000 : ℝ) := by
    have hpowers : (33633/50000 : ℝ)^37 ≤ (7989593213909698551/50000000000000000000 : ℝ)^8 := by
      have hnat : (33633 : ℕ)^37*50000000000000000000^8 ≤ 7989593213909698551^8*50000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        33633 50000 7989593213909698551 50000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (33633/50000 : ℝ)) (X := (7989593213909698551/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (57989593213909698551/50000000000000000000 : ℝ) ≤ (10325712113803847/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (57989593213909698551/50000000000000000000 : ℝ)^8 ≤ (10325712113803847/10000000000000000 : ℝ)^37 := by
      have hnat : (57989593213909698551 : ℕ)^8*10000000000000000^37 ≤ 10325712113803847^37*50000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        57989593213909698551 50000000000000000000 10325712113803847 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10325712113803847/10000000000000000 : ℝ)) (X := (57989593213909698551/50000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (32989593213909698551/25000000000000000000 : ℝ) ≤ (10617943792036179/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (32989593213909698551/25000000000000000000 : ℝ)^8 ≤ (10617943792036179/10000000000000000 : ℝ)^37 := by
      have hnat : (32989593213909698551 : ℕ)^8*10000000000000000^37 ≤ 10617943792036179^37*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        32989593213909698551 25000000000000000000 10617943792036179 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10617943792036179/10000000000000000 : ℝ)) (X := (32989593213909698551/25000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(325712113803847/6726600000000000 : ℝ)*((-1 : ℝ)*(X 0 0+X 1 0))+(73057919558083/1681650000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (33633/50000 : ℝ)) (alpha := (325712113803847/6726600000000000 : ℝ)) (beta := (73057919558083/1681650000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]] hX 2 (by
        change ((-1 : ℝ)*pair X 2 0) ≤ (33633/50000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(325712113803847/6726600000000000 : ℝ)*((-1 : ℝ)*pair X 2 0)+(73057919558083/1681650000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-844547161/2500000000 : ℝ)*X 0 0+(3310885283/10000000000 : ℝ)*X 0 1+(-2911958447/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314058_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((1560688329/5000000000 : ℝ)*X 1 0+(-1526181473/5000000000 : ℝ)*X 1 1+(-6258241381/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314058_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((345983109/625000000 : ℝ)*X 2 0+(5268026701/10000000000 : ℝ)*X 2 1+(723713169/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314058_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_6 : ((4410709889/10000000000 : ℝ)*X 0 0+(261738807/400000000 : ℝ)*X 0 1+(-571523901/5000000000 : ℝ)*X 0 2+(4410709889/10000000000 : ℝ)*X 1 0+(261738807/400000000 : ℝ)*X 1 1+(-571523901/5000000000 : ℝ)*X 1 2+(4410709889/10000000000 : ℝ)*X 2 0+(261738807/400000000 : ℝ)*X 2 1+(-571523901/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314058_s1_s1_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-384212051/1250000000 : ℝ)*X 0 0+(707321369/2500000000 : ℝ)*X 0 1+(-323917911/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314058_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((3152082233/10000000000 : ℝ)*X 1 0+(-1427428311/5000000000 : ℝ)*X 1 1+(-6393499793/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314058_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((698748787/1250000000 : ℝ)*X 2 0+(2727270407/5000000000 : ℝ)*X 2 1+(272622773/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314058_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((4119848079/10000000000 : ℝ)*X 0 0+(181083989/250000000 : ℝ)*X 0 1+(-79077187/2500000000 : ℝ)*X 0 2+(4119848079/10000000000 : ℝ)*X 1 0+(181083989/250000000 : ℝ)*X 1 1+(-79077187/2500000000 : ℝ)*X 1 2+(4119848079/10000000000 : ℝ)*X 2 0+(181083989/250000000 : ℝ)*X 2 1+(-79077187/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314058_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-2888249753/10000000000 : ℝ)*X 0 0+(610695443/2000000000 : ℝ)*X 0 1+(-644760921/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314058_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((1423201157/5000000000 : ℝ)*X 1 0+(-608123919/2000000000 : ℝ)*X 1 1+(-6491652789/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314058_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((1200233707/2000000000 : ℝ)*X 2 0+(5192239319/10000000000 : ℝ)*X 2 1+(209633313/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314058_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((225358421/500000000 : ℝ)*X 0 0+(3420952199/5000000000 : ℝ)*X 0 1+(-226809759/5000000000 : ℝ)*X 0 2+(225358421/500000000 : ℝ)*X 1 0+(3420952199/5000000000 : ℝ)*X 1 1+(-226809759/5000000000 : ℝ)*X 1 2+(225358421/500000000 : ℝ)*X 2 0+(3420952199/5000000000 : ℝ)*X 2 1+(-226809759/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314058_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-3324445119/10000000000 : ℝ)*X 0 0+(816318109/2500000000 : ℝ)*X 0 1+(-5909074711/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314058_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((638758783/2000000000 : ℝ)*X 1 0+(-623250993/2000000000 : ℝ)*X 1 1+(-6145071237/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314058_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((3119541739/5000000000 : ℝ)*X 2 0+(1123591243/2500000000 : ℝ)*X 2 1+(298778399/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314058_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((13073323/40000000 : ℝ)*X 0 0+(1965403021/2500000000 : ℝ)*X 0 1+(-1951167/39062500 : ℝ)*X 0 2+(13073323/40000000 : ℝ)*X 1 0+(1965403021/2500000000 : ℝ)*X 1 1+(-1951167/39062500 : ℝ)*X 1 2+(13073323/40000000 : ℝ)*X 2 0+(1965403021/2500000000 : ℝ)*X 2 1+(-1951167/39062500 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314058_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((41937/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(41937/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (312147222421884718316004138799/31856794744350000000000000000000000 : ℝ) := by norm_num
    linear_combination (15304564313/200000000000 : ℝ)*(base5) + (766407/200000000000 : ℝ)*(base59) + (2289522468123/1000000000000 : ℝ)*(base60) + (5053173226871/500000000000 : ℝ)*(major_s1_0) + (5053173226871/500000000000 : ℝ)*(major_s1_1) + (5053173226871/500000000000 : ℝ)*(major_s1_2) + (66801269/1000000000000 : ℝ)*(sp_s1_1) + (177871939/1000000000000 : ℝ)*(sp_s1_2) + (3584815754899/250000000000 : ℝ)*(sp_s1_7) + (1792387108361/125000000000 : ℝ)*(sp_s1_8) + (14415607969221/1000000000000 : ℝ)*(sp_s1_9) + (5796832113911/1000000000000 : ℝ)*(sp_s1_13) + (1241893/12500000000 : ℝ)*(sp_s1_15) + (71686253/1000000000000 : ℝ)*(sp_s1_20) + (183544581929/31250000000 : ℝ)*(f.failure) + (3584815754899/250000000000 : ℝ)*(f.sum) + (1971884632802329243/4880148300000000000000000000000 : ℝ)*base62 + (75497473712291/420412500000000000000000000 : ℝ)*base64 + (4864144094681/1922575000000000000000000000 : ℝ)*base67 + (2344164297560087/3363300000000000000000000000 : ℝ)*base68 + (2152760613911046013/19883829600000000000000000000000 : ℝ)*base71 + (75523734823119/118240000000000000000000000 : ℝ)*base73 + (1328026019149/4534375000000000000000000 : ℝ)*base75 + (137010002242093/591200000000000000000000000 : ℝ)*base77 + (3713700804145319933/45465053600000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base83 + (1/1000000000000 : ℝ)*base84 + (2649/3125000000000000 : ℝ)*base86 + (2649/3125000000000000 : ℝ)*base88 + (2649/3125000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18341/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18341/50000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (13009811957694035410833117/1933150100000000000000000000000 : ℝ) := by norm_num
    linear_combination (2195600604461/500000000000 : ℝ)*(base5) + (82251608957/500000000000 : ℝ)*(base49) + (2274833944541/500000000000 : ℝ)*(base60) + (2248647095819/250000000000 : ℝ)*(major_s1_0) + (2248647095819/250000000000 : ℝ)*(major_s1_1) + (2248647095819/250000000000 : ℝ)*(major_s1_2) + (2346969/100000000000 : ℝ)*(sp_s1_6) + (6141629/62500000000 : ℝ)*(sp_s1_7) + (12761749188917/1000000000000 : ℝ)*(sp_s1_14) + (1276185967673/100000000000 : ℝ)*(sp_s1_15) + (17153030822823/1000000000000 : ℝ)*(sp_s1_16) + (836090167919/1000000000000 : ℝ)*(sp_s1_20) + (3055437/250000000000 : ℝ)*(sp_s1_21) + (7515707/250000000000 : ℝ)*(sp_s1_23) + (522731484653/100000000000 : ℝ)*(f.failure) + (1276185967673/100000000000 : ℝ)*(f.sum) + (552045757607693983/610018537500000000000000000000 : ℝ)*base62 + (982019078144827/1681650000000000000000000000 : ℝ)*base64 + (332570516954551/961287500000000000000000000 : ℝ)*base66 + (1264548547171343/1681650000000000000000000000 : ℝ)*base68 + (49347083579632362401/69593403600000000000000000000000 : ℝ)*base70 + (19388384075937/82768000000000000000000000 : ℝ)*base73 + (1365641391397/72550000000000000000000000 : ℝ)*base75 + (390969317212441/2069200000000000000000000000 : ℝ)*base76 + (24539687384983679679/159127687600000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (2943/10000000000000000 : ℝ)*base86 + (2943/10000000000000000 : ℝ)*base88 + (2943/10000000000000000 : ℝ)*base90 + (1/1000000000000 : ℝ)*base93 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-6577/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-6577/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (418455466073786716979611483179/33980581060640000000000000000000000 : ℝ) := by norm_num
    linear_combination (6360851/1000000000000 : ℝ)*(base5) + (2405361/1000000000000 : ℝ)*(base16) + (122895554419/500000000000 : ℝ)*(base49) + (665547583009/1000000000000 : ℝ)*(base60) + (5399094520239/1000000000000 : ℝ)*(major_s1_0) + (5399094520239/1000000000000 : ℝ)*(major_s1_1) + (5399094520239/1000000000000 : ℝ)*(major_s1_2) + (54989517/125000000000 : ℝ)*(sp_s1_0) + (157572411/1000000000000 : ℝ)*(sp_s1_2) + (140458133/1000000000000 : ℝ)*(sp_s1_13) + (1531999065183/200000000000 : ℝ)*(sp_s1_21) + (766043283669/100000000000 : ℝ)*(sp_s1_22) + (7660284030491/1000000000000 : ℝ)*(sp_s1_23) + (98050089831/31250000000 : ℝ)*(sp_s1_27) + (392218711697/125000000000 : ℝ)*(f.failure) + (7660435242051/1000000000000 : ℝ)*(f.sum) + (215404040704905401/3253432200000000000000000000000 : ℝ)*base63 + (145542926016299/560550000000000000000000000 : ℝ)*base65 + (158112877426149/3845150000000000000000000000 : ℝ)*base67 + (792191066703649/2242200000000000000000000000 : ℝ)*base69 + (1526466370057522039/13255886400000000000000000000000 : ℝ)*base71 + (14997694162613/47296000000000000000000000 : ℝ)*base72 + (23718400044661/145100000000000000000000000 : ℝ)*base75 + (61184222949957/1182400000000000000000000000 : ℝ)*base77 + (28218458071220719877/90930107200000000000000000000000 : ℝ)*base79 + (3593/12500000000000000 : ℝ)*base87 + (3593/12500000000000000 : ℝ)*base89 + (3593/12500000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![false, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((5173/6250 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(5173/6250 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(76903/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(76903/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-33633/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-33633/50000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((41937/100000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(41937/100000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(18341/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(18341/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((1 : ℝ)*X 0 0+(-6577/50000 : ℝ)*X 0 2+(1 : ℝ)*X 1 0+(-6577/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c314058_s1 p hpa hpb X hX hprev0

#print axioms solution
