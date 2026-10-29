-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c314062_s1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:47:50.549618+00:00
-- url     : https://prove2.me/submissions/131fea05-f500-4298-b568-651ee0911195

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
theorem collision_support_c314062_s1_s1_0 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1255892429/10000000000 : ℝ)*x 0 + (502827079/1000000000 : ℝ)*x 1 + (-1474573159/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1255892429/10000000000 : ℝ)^75 ≤ (7154850478079/100000000000000 : ℝ)^59 := by
    have hnat : (1255892429 : ℕ)^75*100000000000000^59 ≤ 7154850478079^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255892429 10000000000 7154850478079 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (502827079/1000000000 : ℝ)^75 ≤ (1669196394059/4000000000000 : ℝ)^59 := by
    have hnat : (502827079 : ℕ)^75*4000000000000^59 ≤ 1669196394059^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502827079 1000000000 1669196394059 4000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1474573159/2500000000 : ℝ)^75 ≤ (51115239652081/100000000000000 : ℝ)^59 := by
    have hnat : (1474573159 : ℕ)^75*100000000000000^59 ≤ 51115239652081^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1474573159 2500000000 51115239652081 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1255892429/10000000000 : ℝ), (502827079/1000000000 : ℝ), (-1474573159/2500000000 : ℝ)] ![(7154850478079/100000000000000 : ℝ), (1669196394059/4000000000000 : ℝ), (51115239652081/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1255892429/10000000000 : ℝ)|^75 ≤ (7154850478079/100000000000000 : ℝ)^59
        have hw : |(-1255892429/10000000000 : ℝ)|=(1255892429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(502827079/1000000000 : ℝ)|^75 ≤ (1669196394059/4000000000000 : ℝ)^59
        have hw : |(502827079/1000000000 : ℝ)|=(502827079/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1474573159/2500000000 : ℝ)|^75 ≤ (51115239652081/100000000000000 : ℝ)^59
        have hw : |(-1474573159/2500000000 : ℝ)|=(1474573159/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314062_s1_s1_1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2528873483/5000000000 : ℝ)*x 0 + (-1268490527/10000000000 : ℝ)*x 1 + (-5861718591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2528873483/5000000000 : ℝ)^75 ≤ (21020560002351/50000000000000 : ℝ)^59 := by
    have hnat : (2528873483 : ℕ)^75*50000000000000^59 ≤ 21020560002351^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2528873483 5000000000 21020560002351 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1268490527/10000000000 : ℝ)^75 ≤ (7246209455951/100000000000000 : ℝ)^59 := by
    have hnat : (1268490527 : ℕ)^75*100000000000000^59 ≤ 7246209455951^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1268490527 10000000000 7246209455951 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5861718591/10000000000 : ℝ)^75 ≤ (12678167628299/25000000000000 : ℝ)^59 := by
    have hnat : (5861718591 : ℕ)^75*25000000000000^59 ≤ 12678167628299^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5861718591 10000000000 12678167628299 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2528873483/5000000000 : ℝ), (-1268490527/10000000000 : ℝ), (-5861718591/10000000000 : ℝ)] ![(21020560002351/50000000000000 : ℝ), (7246209455951/100000000000000 : ℝ), (12678167628299/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2528873483/5000000000 : ℝ)|^75 ≤ (21020560002351/50000000000000 : ℝ)^59
        have hw : |(2528873483/5000000000 : ℝ)|=(2528873483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1268490527/10000000000 : ℝ)|^75 ≤ (7246209455951/100000000000000 : ℝ)^59
        have hw : |(-1268490527/10000000000 : ℝ)|=(1268490527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5861718591/10000000000 : ℝ)|^75 ≤ (12678167628299/25000000000000 : ℝ)^59
        have hw : |(-5861718591/10000000000 : ℝ)|=(5861718591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314062_s1_s1_2 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2639842201/5000000000 : ℝ)*x 0 + (5314680721/10000000000 : ℝ)*x 1 + (1739537097/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639842201/5000000000 : ℝ)^75 ≤ (44400003439597/100000000000000 : ℝ)^59 := by
    have hnat : (2639842201 : ℕ)^75*100000000000000^59 ≤ 44400003439597^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639842201 5000000000 44400003439597 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5314680721/10000000000 : ℝ)^75 ≤ (2798403466987/6250000000000 : ℝ)^59 := by
    have hnat : (5314680721 : ℕ)^75*6250000000000^59 ≤ 2798403466987^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5314680721 10000000000 2798403466987 6250000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1739537097/10000000000 : ℝ)^75 ≤ (10825541072937/100000000000000 : ℝ)^59 := by
    have hnat : (1739537097 : ℕ)^75*100000000000000^59 ≤ 10825541072937^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1739537097 10000000000 10825541072937 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639842201/5000000000 : ℝ), (5314680721/10000000000 : ℝ), (1739537097/10000000000 : ℝ)] ![(44400003439597/100000000000000 : ℝ), (2798403466987/6250000000000 : ℝ), (10825541072937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639842201/5000000000 : ℝ)|^75 ≤ (44400003439597/100000000000000 : ℝ)^59
        have hw : |(2639842201/5000000000 : ℝ)|=(2639842201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5314680721/10000000000 : ℝ)|^75 ≤ (2798403466987/6250000000000 : ℝ)^59
        have hw : |(5314680721/10000000000 : ℝ)|=(5314680721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1739537097/10000000000 : ℝ)|^75 ≤ (10825541072937/100000000000000 : ℝ)^59
        have hw : |(1739537097/10000000000 : ℝ)|=(1739537097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314062_s1_s1_7 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1346346873/10000000000 : ℝ)*x 0 + (3605049027/10000000000 : ℝ)*x 1 + (-3556220971/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1346346873/10000000000 : ℝ)^75 ≤ (7816208633159/100000000000000 : ℝ)^59 := by
    have hnat : (1346346873 : ℕ)^75*100000000000000^59 ≤ 7816208633159^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346346873 10000000000 7816208633159 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3605049027/10000000000 : ℝ)^75 ≤ (27337040364161/100000000000000 : ℝ)^59 := by
    have hnat : (3605049027 : ℕ)^75*100000000000000^59 ≤ 27337040364161^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3605049027 10000000000 27337040364161 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3556220971/5000000000 : ℝ)^75 ≤ (8105843874587/12500000000000 : ℝ)^59 := by
    have hnat : (3556220971 : ℕ)^75*12500000000000^59 ≤ 8105843874587^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3556220971 5000000000 8105843874587 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1346346873/10000000000 : ℝ), (3605049027/10000000000 : ℝ), (-3556220971/5000000000 : ℝ)] ![(7816208633159/100000000000000 : ℝ), (27337040364161/100000000000000 : ℝ), (8105843874587/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1346346873/10000000000 : ℝ)|^75 ≤ (7816208633159/100000000000000 : ℝ)^59
        have hw : |(-1346346873/10000000000 : ℝ)|=(1346346873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3605049027/10000000000 : ℝ)|^75 ≤ (27337040364161/100000000000000 : ℝ)^59
        have hw : |(3605049027/10000000000 : ℝ)|=(3605049027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3556220971/5000000000 : ℝ)|^75 ≤ (8105843874587/12500000000000 : ℝ)^59
        have hw : |(-3556220971/5000000000 : ℝ)|=(3556220971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314062_s1_s1_8 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (127153751/312500000 : ℝ)*x 0 + (-349701781/5000000000 : ℝ)*x 1 + (-3550586701/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (127153751/312500000 : ℝ)^75 ≤ (31884175907973/100000000000000 : ℝ)^59 := by
    have hnat : (127153751 : ℕ)^75*100000000000000^59 ≤ 31884175907973^59*312500000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127153751 312500000 31884175907973 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (349701781/5000000000 : ℝ)^75 ≤ (3399645981957/100000000000000 : ℝ)^59 := by
    have hnat : (349701781 : ℕ)^75*100000000000000^59 ≤ 3399645981957^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349701781 5000000000 3399645981957 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3550586701/5000000000 : ℝ)^75 ≤ (64716178097859/100000000000000 : ℝ)^59 := by
    have hnat : (3550586701 : ℕ)^75*100000000000000^59 ≤ 64716178097859^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3550586701 5000000000 64716178097859 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(127153751/312500000 : ℝ), (-349701781/5000000000 : ℝ), (-3550586701/5000000000 : ℝ)] ![(31884175907973/100000000000000 : ℝ), (3399645981957/100000000000000 : ℝ), (64716178097859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(127153751/312500000 : ℝ)|^75 ≤ (31884175907973/100000000000000 : ℝ)^59
        have hw : |(127153751/312500000 : ℝ)|=(127153751/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-349701781/5000000000 : ℝ)|^75 ≤ (3399645981957/100000000000000 : ℝ)^59
        have hw : |(-349701781/5000000000 : ℝ)|=(349701781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3550586701/5000000000 : ℝ)|^75 ≤ (64716178097859/100000000000000 : ℝ)^59
        have hw : |(-3550586701/5000000000 : ℝ)|=(3550586701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314062_s1_s1_9 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4088761439/10000000000 : ℝ)*x 0 + (1708575831/2500000000 : ℝ)*x 1 + (1133094723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4088761439/10000000000 : ℝ)^75 ≤ (32081947759667/100000000000000 : ℝ)^59 := by
    have hnat : (4088761439 : ℕ)^75*100000000000000^59 ≤ 32081947759667^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4088761439 10000000000 32081947759667 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1708575831/2500000000 : ℝ)^75 ≤ (12328083512303/20000000000000 : ℝ)^59 := by
    have hnat : (1708575831 : ℕ)^75*20000000000000^59 ≤ 12328083512303^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1708575831 2500000000 12328083512303 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1133094723/10000000000 : ℝ)^75 ≤ (784704334483/12500000000000 : ℝ)^59 := by
    have hnat : (1133094723 : ℕ)^75*12500000000000^59 ≤ 784704334483^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133094723 10000000000 784704334483 12500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4088761439/10000000000 : ℝ), (1708575831/2500000000 : ℝ), (1133094723/10000000000 : ℝ)] ![(32081947759667/100000000000000 : ℝ), (12328083512303/20000000000000 : ℝ), (784704334483/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4088761439/10000000000 : ℝ)|^75 ≤ (32081947759667/100000000000000 : ℝ)^59
        have hw : |(4088761439/10000000000 : ℝ)|=(4088761439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1708575831/2500000000 : ℝ)|^75 ≤ (12328083512303/20000000000000 : ℝ)^59
        have hw : |(1708575831/2500000000 : ℝ)|=(1708575831/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1133094723/10000000000 : ℝ)|^75 ≤ (784704334483/12500000000000 : ℝ)^59
        have hw : |(1133094723/10000000000 : ℝ)|=(1133094723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314062_s1_s1_13 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4463800447/10000000000 : ℝ)*x 0 + (352043841/500000000 : ℝ)*x 1 + (-24087929/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4463800447/10000000000 : ℝ)^75 ≤ (35868189461027/100000000000000 : ℝ)^59 := by
    have hnat : (4463800447 : ℕ)^75*100000000000000^59 ≤ 35868189461027^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4463800447 10000000000 35868189461027 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (352043841/500000000 : ℝ)^75 ≤ (64018454601923/100000000000000 : ℝ)^59 := by
    have hnat : (352043841 : ℕ)^75*100000000000000^59 ≤ 64018454601923^59*500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352043841 500000000 64018454601923 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (24087929/5000000000 : ℝ)^75 ≤ (113355925307/100000000000000 : ℝ)^59 := by
    have hnat : (24087929 : ℕ)^75*100000000000000^59 ≤ 113355925307^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      24087929 5000000000 113355925307 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4463800447/10000000000 : ℝ), (352043841/500000000 : ℝ), (-24087929/5000000000 : ℝ)] ![(35868189461027/100000000000000 : ℝ), (64018454601923/100000000000000 : ℝ), (113355925307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4463800447/10000000000 : ℝ)|^75 ≤ (35868189461027/100000000000000 : ℝ)^59
        have hw : |(4463800447/10000000000 : ℝ)|=(4463800447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(352043841/500000000 : ℝ)|^75 ≤ (64018454601923/100000000000000 : ℝ)^59
        have hw : |(352043841/500000000 : ℝ)|=(352043841/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-24087929/5000000000 : ℝ)|^75 ≤ (113355925307/100000000000000 : ℝ)^59
        have hw : |(-24087929/5000000000 : ℝ)|=(24087929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314062_s1_s1_14 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-690706569/10000000000 : ℝ)*x 0 + (501964933/1250000000 : ℝ)*x 1 + (-3575709127/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (690706569/10000000000 : ℝ)^75 ≤ (104562453967/3125000000000 : ℝ)^59 := by
    have hnat : (690706569 : ℕ)^75*3125000000000^59 ≤ 104562453967^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      690706569 10000000000 104562453967 3125000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (501964933/1250000000 : ℝ)^75 ≤ (3135518467917/10000000000000 : ℝ)^59 := by
    have hnat : (501964933 : ℕ)^75*10000000000000^59 ≤ 3135518467917^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      501964933 1250000000 3135518467917 10000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3575709127/5000000000 : ℝ)^75 ≤ (65298816781331/100000000000000 : ℝ)^59 := by
    have hnat : (3575709127 : ℕ)^75*100000000000000^59 ≤ 65298816781331^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3575709127 5000000000 65298816781331 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-690706569/10000000000 : ℝ), (501964933/1250000000 : ℝ), (-3575709127/5000000000 : ℝ)] ![(104562453967/3125000000000 : ℝ), (3135518467917/10000000000000 : ℝ), (65298816781331/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-690706569/10000000000 : ℝ)|^75 ≤ (104562453967/3125000000000 : ℝ)^59
        have hw : |(-690706569/10000000000 : ℝ)|=(690706569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(501964933/1250000000 : ℝ)|^75 ≤ (3135518467917/10000000000000 : ℝ)^59
        have hw : |(501964933/1250000000 : ℝ)|=(501964933/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3575709127/5000000000 : ℝ)|^75 ≤ (65298816781331/100000000000000 : ℝ)^59
        have hw : |(-3575709127/5000000000 : ℝ)|=(3575709127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314062_s1_s1_15 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3566309209/10000000000 : ℝ)*x 0 + (-169180419/1250000000 : ℝ)*x 1 + (-357003931/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3566309209/10000000000 : ℝ)^75 ≤ (5392831535393/20000000000000 : ℝ)^59 := by
    have hnat : (3566309209 : ℕ)^75*20000000000000^59 ≤ 5392831535393^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3566309209 10000000000 5392831535393 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169180419/1250000000 : ℝ)^75 ≤ (1573723414669/20000000000000 : ℝ)^59 := by
    have hnat : (169180419 : ℕ)^75*20000000000000^59 ≤ 1573723414669^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169180419 1250000000 1573723414669 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (357003931/500000000 : ℝ)^75 ≤ (32583612615787/50000000000000 : ℝ)^59 := by
    have hnat : (357003931 : ℕ)^75*50000000000000^59 ≤ 32583612615787^59*500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357003931 500000000 32583612615787 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3566309209/10000000000 : ℝ), (-169180419/1250000000 : ℝ), (-357003931/500000000 : ℝ)] ![(5392831535393/20000000000000 : ℝ), (1573723414669/20000000000000 : ℝ), (32583612615787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3566309209/10000000000 : ℝ)|^75 ≤ (5392831535393/20000000000000 : ℝ)^59
        have hw : |(3566309209/10000000000 : ℝ)|=(3566309209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-169180419/1250000000 : ℝ)|^75 ≤ (1573723414669/20000000000000 : ℝ)^59
        have hw : |(-169180419/1250000000 : ℝ)|=(169180419/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-357003931/500000000 : ℝ)|^75 ≤ (32583612615787/50000000000000 : ℝ)^59
        have hw : |(-357003931/500000000 : ℝ)|=(357003931/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314062_s1_s1_16 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6609047859/10000000000 : ℝ)*x 0 + (541952187/1250000000 : ℝ)*x 1 + (1145698257/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6609047859/10000000000 : ℝ)^75 ≤ (11813892102077/20000000000000 : ℝ)^59 := by
    have hnat : (6609047859 : ℕ)^75*20000000000000^59 ≤ 11813892102077^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6609047859 10000000000 11813892102077 20000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541952187/1250000000 : ℝ)^75 ≤ (864100209821/2500000000000 : ℝ)^59 := by
    have hnat : (541952187 : ℕ)^75*2500000000000^59 ≤ 864100209821^59*1250000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541952187 1250000000 864100209821 2500000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1145698257/10000000000 : ℝ)^75 ≤ (3183265537431/50000000000000 : ℝ)^59 := by
    have hnat : (1145698257 : ℕ)^75*50000000000000^59 ≤ 3183265537431^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1145698257 10000000000 3183265537431 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6609047859/10000000000 : ℝ), (541952187/1250000000 : ℝ), (1145698257/10000000000 : ℝ)] ![(11813892102077/20000000000000 : ℝ), (864100209821/2500000000000 : ℝ), (3183265537431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6609047859/10000000000 : ℝ)|^75 ≤ (11813892102077/20000000000000 : ℝ)^59
        have hw : |(6609047859/10000000000 : ℝ)|=(6609047859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541952187/1250000000 : ℝ)|^75 ≤ (864100209821/2500000000000 : ℝ)^59
        have hw : |(541952187/1250000000 : ℝ)|=(541952187/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1145698257/10000000000 : ℝ)|^75 ≤ (3183265537431/50000000000000 : ℝ)^59
        have hw : |(1145698257/10000000000 : ℝ)|=(1145698257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314062_s1_s1_20 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (7474467947/10000000000 : ℝ)*x 0 + (791746217/2000000000 : ℝ)*x 1 + (-439793/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7474467947/10000000000 : ℝ)^75 ≤ (69071195187249/100000000000000 : ℝ)^59 := by
    have hnat : (7474467947 : ℕ)^75*100000000000000^59 ≤ 69071195187249^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7474467947 10000000000 69071195187249 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (791746217/2000000000 : ℝ)^75 ≤ (30790635014911/100000000000000 : ℝ)^59 := by
    have hnat : (791746217 : ℕ)^75*100000000000000^59 ≤ 30790635014911^59*2000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      791746217 2000000000 30790635014911 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (439793/78125000 : ℝ)^75 ≤ (34542445363/25000000000000 : ℝ)^59 := by
    have hnat : (439793 : ℕ)^75*25000000000000^59 ≤ 34542445363^59*78125000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439793 78125000 34542445363 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(7474467947/10000000000 : ℝ), (791746217/2000000000 : ℝ), (-439793/78125000 : ℝ)] ![(69071195187249/100000000000000 : ℝ), (30790635014911/100000000000000 : ℝ), (34542445363/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(7474467947/10000000000 : ℝ)|^75 ≤ (69071195187249/100000000000000 : ℝ)^59
        have hw : |(7474467947/10000000000 : ℝ)|=(7474467947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(791746217/2000000000 : ℝ)|^75 ≤ (30790635014911/100000000000000 : ℝ)^59
        have hw : |(791746217/2000000000 : ℝ)|=(791746217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-439793/78125000 : ℝ)|^75 ≤ (34542445363/25000000000000 : ℝ)^59
        have hw : |(-439793/78125000 : ℝ)|=(439793/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314062_s1_s1_21 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-168984689/10000000000 : ℝ)*x 0 + (6003522527/10000000000 : ℝ)*x 1 + (-173017413/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168984689/10000000000 : ℝ)^75 ≤ (279404626753/50000000000000 : ℝ)^59 := by
    have hnat : (168984689 : ℕ)^75*50000000000000^59 ≤ 279404626753^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168984689 10000000000 279404626753 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6003522527/10000000000 : ℝ)^75 ≤ (52277269479461/100000000000000 : ℝ)^59 := by
    have hnat : (6003522527 : ℕ)^75*100000000000000^59 ≤ 52277269479461^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6003522527 10000000000 52277269479461 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (173017413/312500000 : ℝ)^75 ≤ (11790980312603/25000000000000 : ℝ)^59 := by
    have hnat : (173017413 : ℕ)^75*25000000000000^59 ≤ 11790980312603^59*312500000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173017413 312500000 11790980312603 25000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-168984689/10000000000 : ℝ), (6003522527/10000000000 : ℝ), (-173017413/312500000 : ℝ)] ![(279404626753/50000000000000 : ℝ), (52277269479461/100000000000000 : ℝ), (11790980312603/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-168984689/10000000000 : ℝ)|^75 ≤ (279404626753/50000000000000 : ℝ)^59
        have hw : |(-168984689/10000000000 : ℝ)|=(168984689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6003522527/10000000000 : ℝ)|^75 ≤ (52277269479461/100000000000000 : ℝ)^59
        have hw : |(6003522527/10000000000 : ℝ)|=(6003522527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-173017413/312500000 : ℝ)|^75 ≤ (11790980312603/25000000000000 : ℝ)^59
        have hw : |(-173017413/312500000 : ℝ)|=(173017413/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314062_s1_s1_22 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6447887441/10000000000 : ℝ)*x 0 + (-297830149/5000000000 : ℝ)*x 1 + (-1215493127/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6447887441/10000000000 : ℝ)^75 ≤ (57244536517177/100000000000000 : ℝ)^59 := by
    have hnat : (6447887441 : ℕ)^75*100000000000000^59 ≤ 57244536517177^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6447887441 10000000000 57244536517177 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (297830149/5000000000 : ℝ)^75 ≤ (1386005341623/50000000000000 : ℝ)^59 := by
    have hnat : (297830149 : ℕ)^75*50000000000000^59 ≤ 1386005341623^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297830149 5000000000 1386005341623 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1215493127/2500000000 : ℝ)^75 ≤ (2498965799233/6250000000000 : ℝ)^59 := by
    have hnat : (1215493127 : ℕ)^75*6250000000000^59 ≤ 2498965799233^59*2500000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1215493127 2500000000 2498965799233 6250000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6447887441/10000000000 : ℝ), (-297830149/5000000000 : ℝ), (-1215493127/2500000000 : ℝ)] ![(57244536517177/100000000000000 : ℝ), (1386005341623/50000000000000 : ℝ), (2498965799233/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6447887441/10000000000 : ℝ)|^75 ≤ (57244536517177/100000000000000 : ℝ)^59
        have hw : |(6447887441/10000000000 : ℝ)|=(6447887441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-297830149/5000000000 : ℝ)|^75 ≤ (1386005341623/50000000000000 : ℝ)^59
        have hw : |(-297830149/5000000000 : ℝ)|=(297830149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1215493127/2500000000 : ℝ)|^75 ≤ (2498965799233/6250000000000 : ℝ)^59
        have hw : |(-1215493127/2500000000 : ℝ)|=(1215493127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314062_s1_s1_23 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4180280977/10000000000 : ℝ)*x 0 + (3151844449/5000000000 : ℝ)*x 1 + (1809291941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4180280977/10000000000 : ℝ)^75 ≤ (16498768879243/50000000000000 : ℝ)^59 := by
    have hnat : (4180280977 : ℕ)^75*50000000000000^59 ≤ 16498768879243^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4180280977 10000000000 16498768879243 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3151844449/5000000000 : ℝ)^75 ≤ (27811063410767/50000000000000 : ℝ)^59 := by
    have hnat : (3151844449 : ℕ)^75*50000000000000^59 ≤ 27811063410767^59*5000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3151844449 5000000000 27811063410767 50000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1809291941/10000000000 : ℝ)^75 ≤ (11380335406307/100000000000000 : ℝ)^59 := by
    have hnat : (1809291941 : ℕ)^75*100000000000000^59 ≤ 11380335406307^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1809291941 10000000000 11380335406307 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4180280977/10000000000 : ℝ), (3151844449/5000000000 : ℝ), (1809291941/10000000000 : ℝ)] ![(16498768879243/50000000000000 : ℝ), (27811063410767/50000000000000 : ℝ), (11380335406307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4180280977/10000000000 : ℝ)|^75 ≤ (16498768879243/50000000000000 : ℝ)^59
        have hw : |(4180280977/10000000000 : ℝ)|=(4180280977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3151844449/5000000000 : ℝ)|^75 ≤ (27811063410767/50000000000000 : ℝ)^59
        have hw : |(3151844449/5000000000 : ℝ)|=(3151844449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1809291941/10000000000 : ℝ)|^75 ≤ (11380335406307/100000000000000 : ℝ)^59
        have hw : |(1809291941/10000000000 : ℝ)|=(1809291941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c314062_s1_s1_27 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ)) (x : Fin 3 → ℝ) :
    (786721877/1000000000 : ℝ)*x 0 + (3414368201/10000000000 : ℝ)*x 1 + (-21753701/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (786721877/1000000000 : ℝ)^75 ≤ (2303665287127/3125000000000 : ℝ)^59 := by
    have hnat : (786721877 : ℕ)^75*3125000000000^59 ≤ 2303665287127^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      786721877 1000000000 2303665287127 3125000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3414368201/10000000000 : ℝ)^75 ≤ (25512349089533/100000000000000 : ℝ)^59 := by
    have hnat : (3414368201 : ℕ)^75*100000000000000^59 ≤ 25512349089533^59*10000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3414368201 10000000000 25512349089533 100000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21753701/1000000000 : ℝ)^75 ≤ (30814468399/4000000000000 : ℝ)^59 := by
    have hnat : (21753701 : ℕ)^75*4000000000000^59 ≤ 30814468399^59*1000000000^75 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21753701 1000000000 30814468399 4000000000000 75 59 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (75/16 : ℝ)) 75 59 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(786721877/1000000000 : ℝ), (3414368201/10000000000 : ℝ), (-21753701/1000000000 : ℝ)] ![(2303665287127/3125000000000 : ℝ), (25512349089533/100000000000000 : ℝ), (30814468399/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(786721877/1000000000 : ℝ)|^75 ≤ (2303665287127/3125000000000 : ℝ)^59
        have hw : |(786721877/1000000000 : ℝ)|=(786721877/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3414368201/10000000000 : ℝ)|^75 ≤ (25512349089533/100000000000000 : ℝ)^59
        have hw : |(3414368201/10000000000 : ℝ)|=(3414368201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-21753701/1000000000 : ℝ)|^75 ≤ (30814468399/4000000000000 : ℝ)^59
        have hw : |(-21753701/1000000000 : ℝ)|=(21753701/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c314062_s1 (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((40849/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40849/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40491/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(40491/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-70401/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-70401/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2373/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2373/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59533/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(59533/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-44133/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-44133/100000 : ℝ)*X 1 2) := by
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
  have order2 : 0 ≤ ((1 : ℝ)*(X 0 1+X 1 1)) ∧ ((1 : ℝ)*(X 0 1+X 1 1)) ≤ ((1 : ℝ)*(X 0 0+X 1 0)) ∧ ((1 : ℝ)*(X 0 0+X 1 0)) ≤ ((-1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.ordered 2
    change 0 ≤ ((1 : ℝ)*pair X 2 1) ∧ ((1 : ℝ)*pair X 2 1) ≤ ((1 : ℝ)*pair X 2 0) ∧ ((1 : ℝ)*pair X 2 0) ≤ ((-1 : ℝ)*pair X 2 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have base7 : ((1 : ℝ)*T) ≤ (87867/50000 : ℝ) := by
    linarith only [f.Tcap]
  have base11 : ((1 : ℝ)*X 0 1+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 1).2]
  have base39 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [order0.1]
  have base59 : ((-1 : ℝ)*X 0 1+(-1 : ℝ)*X 1 1) ≤ (0 : ℝ) := by
    linarith only [order2.1]
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
  have s1_pow0 : (40849/50000 : ℝ) ^ (37/8 : ℝ) ≤ (4907811268523967/12500000000000000 : ℝ) := by
    have hpowers : (40849/50000 : ℝ)^37 ≤ (4907811268523967/12500000000000000 : ℝ)^8 := by
      have hnat : (40849 : ℕ)^37*12500000000000000^8 ≤ 4907811268523967^8*50000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40849 50000 4907811268523967 12500000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (40849/50000 : ℝ)) (X := (4907811268523967/12500000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0a : (17407811268523967/12500000000000000 : ℝ) ≤ (2685587369673531/2500000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (17407811268523967/12500000000000000 : ℝ)^8 ≤ (2685587369673531/2500000000000000 : ℝ)^37 := by
      have hnat : (17407811268523967 : ℕ)^8*2500000000000000^37 ≤ 2685587369673531^37*12500000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17407811268523967 12500000000000000 2685587369673531 2500000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2685587369673531/2500000000000000 : ℝ)) (X := (17407811268523967/12500000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner0b : (11157811268523967/6250000000000000 : ℝ) ≤ (11334996857725061/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (11157811268523967/6250000000000000 : ℝ)^8 ≤ (11334996857725061/10000000000000000 : ℝ)^37 := by
      have hnat : (11157811268523967 : ℕ)^8*10000000000000000^37 ≤ 11334996857725061^37*6250000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11157811268523967 6250000000000000 11334996857725061 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11334996857725061/10000000000000000 : ℝ)) (X := (11157811268523967/6250000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(185587369673531/2042450000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(592647379030937/8169800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (40849/50000 : ℝ)) (alpha := (185587369673531/2042450000000000 : ℝ)) (beta := (592647379030937/8169800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow0,s1_corner0a]) (by linarith only [s1_pow0,s1_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (40849/50000 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(185587369673531/2042450000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(592647379030937/8169800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow1 : (40491/50000 : ℝ) ^ (37/8 : ℝ) ≤ (7539226659652356569/20000000000000000000 : ℝ) := by
    have hpowers : (40491/50000 : ℝ)^37 ≤ (7539226659652356569/20000000000000000000 : ℝ)^8 := by
      have hnat : (40491 : ℕ)^37*20000000000000000000^8 ≤ 7539226659652356569^8*50000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        40491 50000 7539226659652356569 20000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (40491/50000 : ℝ)) (X := (7539226659652356569/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1a : (27539226659652356569/20000000000000000000 : ℝ) ≤ (669756830369227/625000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (27539226659652356569/20000000000000000000 : ℝ)^8 ≤ (669756830369227/625000000000000 : ℝ)^37 := by
      have hnat : (27539226659652356569 : ℕ)^8*625000000000000^37 ≤ 669756830369227^37*20000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27539226659652356569 20000000000000000000 669756830369227 625000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (669756830369227/625000000000000 : ℝ)) (X := (27539226659652356569/20000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner1b : (17539226659652356569/10000000000000000000 : ℝ) ≤ (11291691756818037/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (17539226659652356569/10000000000000000000 : ℝ)^8 ≤ (11291691756818037/10000000000000000 : ℝ)^37 := by
      have hnat : (17539226659652356569 : ℕ)^8*10000000000000000^37 ≤ 11291691756818037^37*10000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17539226659652356569 10000000000000000000 11291691756818037 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (11291691756818037/10000000000000000 : ℝ)) (X := (17539226659652356569/10000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(14918943456409/168712500000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(115116494182081/1619640000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (40491/50000 : ℝ)) (alpha := (14918943456409/168712500000000 : ℝ)) (beta := (115116494182081/1619640000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow1,s1_corner1a]) (by linarith only [s1_pow1,s1_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (40491/50000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(14918943456409/168712500000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(115116494182081/1619640000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s1_pow2 : (70401/100000 : ℝ) ^ (37/8 : ℝ) ≤ (4931648198491560899/25000000000000000000 : ℝ) := by
    have hpowers : (70401/100000 : ℝ)^37 ≤ (4931648198491560899/25000000000000000000 : ℝ)^8 := by
      have hnat : (70401 : ℕ)^37*25000000000000000000^8 ≤ 4931648198491560899^8*100000^37 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        70401 100000 4931648198491560899 25000000000000000000 37 8 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (70401/100000 : ℝ)) (X := (4931648198491560899/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2a : (29931648198491560899/25000000000000000000 : ℝ) ≤ (10396953000416433/10000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (29931648198491560899/25000000000000000000 : ℝ)^8 ≤ (10396953000416433/10000000000000000 : ℝ)^37 := by
      have hnat : (29931648198491560899 : ℕ)^8*10000000000000000^37 ≤ 10396953000416433^37*25000000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        29931648198491560899 25000000000000000000 10396953000416433 10000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10396953000416433/10000000000000000 : ℝ)) (X := (29931648198491560899/25000000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have s1_corner2b : (17431648198491560899/12500000000000000000 : ℝ) ≤ (5372764130416233/5000000000000000 : ℝ) ^ (37/8 : ℝ) := by
    have hpowers : (17431648198491560899/12500000000000000000 : ℝ)^8 ≤ (5372764130416233/5000000000000000 : ℝ)^37 := by
      have hnat : (17431648198491560899 : ℕ)^8*5000000000000000^37 ≤ 5372764130416233^37*12500000000000000000^8 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17431648198491560899 12500000000000000000 5372764130416233 5000000000000000 8 37 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5372764130416233/5000000000000000 : ℝ)) (X := (17431648198491560899/12500000000000000000 : ℝ)) (by norm_num) 37 8 (by norm_num) hpowers
    exact h
  have major_s1_2 : P 2 ≤ ((-1 : ℝ)*(X 0 2+X 1 2))+(396953000416433/7040100000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(116191753472011/2346700000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (37/8 : ℝ)) (rho := (70401/100000 : ℝ)) (alpha := (396953000416433/7040100000000000 : ℝ)) (beta := (116191753472011/2346700000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s1_pow2,s1_corner2a]) (by linarith only [s1_pow2,s1_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (70401/100000 : ℝ)*((-1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s0_2])
    change lpNorm p (pair X 2) ≤ ((-1 : ℝ)*pair X 2 2)+(396953000416433/7040100000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(116191753472011/2346700000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s1_0 : ((-1255892429/10000000000 : ℝ)*X 0 0+(502827079/1000000000 : ℝ)*X 0 1+(-1474573159/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s1_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_1 : ((2528873483/5000000000 : ℝ)*X 1 0+(-1268490527/10000000000 : ℝ)*X 1 1+(-5861718591/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s1_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_2 : ((2639842201/5000000000 : ℝ)*X 2 0+(5314680721/10000000000 : ℝ)*X 2 1+(1739537097/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s1_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_7 : ((-1346346873/10000000000 : ℝ)*X 0 0+(3605049027/10000000000 : ℝ)*X 0 1+(-3556220971/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s1_s1_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_8 : ((127153751/312500000 : ℝ)*X 1 0+(-349701781/5000000000 : ℝ)*X 1 1+(-3550586701/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s1_s1_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_9 : ((4088761439/10000000000 : ℝ)*X 2 0+(1708575831/2500000000 : ℝ)*X 2 1+(1133094723/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s1_s1_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_13 : ((4463800447/10000000000 : ℝ)*X 0 0+(352043841/500000000 : ℝ)*X 0 1+(-24087929/5000000000 : ℝ)*X 0 2+(4463800447/10000000000 : ℝ)*X 1 0+(352043841/500000000 : ℝ)*X 1 1+(-24087929/5000000000 : ℝ)*X 1 2+(4463800447/10000000000 : ℝ)*X 2 0+(352043841/500000000 : ℝ)*X 2 1+(-24087929/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s1_s1_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_14 : ((-690706569/10000000000 : ℝ)*X 0 0+(501964933/1250000000 : ℝ)*X 0 1+(-3575709127/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s1_s1_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_15 : ((3566309209/10000000000 : ℝ)*X 1 0+(-169180419/1250000000 : ℝ)*X 1 1+(-357003931/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s1_s1_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_16 : ((6609047859/10000000000 : ℝ)*X 2 0+(541952187/1250000000 : ℝ)*X 2 1+(1145698257/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s1_s1_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_20 : ((7474467947/10000000000 : ℝ)*X 0 0+(791746217/2000000000 : ℝ)*X 0 1+(-439793/78125000 : ℝ)*X 0 2+(7474467947/10000000000 : ℝ)*X 1 0+(791746217/2000000000 : ℝ)*X 1 1+(-439793/78125000 : ℝ)*X 1 2+(7474467947/10000000000 : ℝ)*X 2 0+(791746217/2000000000 : ℝ)*X 2 1+(-439793/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s1_s1_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_21 : ((-168984689/10000000000 : ℝ)*X 0 0+(6003522527/10000000000 : ℝ)*X 0 1+(-173017413/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s1_s1_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_22 : ((6447887441/10000000000 : ℝ)*X 1 0+(-297830149/5000000000 : ℝ)*X 1 1+(-1215493127/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s1_s1_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_23 : ((4180280977/10000000000 : ℝ)*X 2 0+(3151844449/5000000000 : ℝ)*X 2 1+(1809291941/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s1_s1_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s1_27 : ((786721877/1000000000 : ℝ)*X 0 0+(3414368201/10000000000 : ℝ)*X 0 1+(-21753701/1000000000 : ℝ)*X 0 2+(786721877/1000000000 : ℝ)*X 1 0+(3414368201/10000000000 : ℝ)*X 1 1+(-21753701/1000000000 : ℝ)*X 1 2+(786721877/1000000000 : ℝ)*X 2 0+(3414368201/10000000000 : ℝ)*X 2 1+(-21753701/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c314062_s1_s1_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s1_0 : (0 : ℝ) ≤ ((2373/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2373/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (329385887370953040705529311811/21563785350085000000000000000000000 : ℝ) := by norm_num
    linear_combination (577214379507/1000000000000 : ℝ)*(base7) + (197253/250000000000 : ℝ)*(base39) + (42183406679/500000000000 : ℝ)*(base60) + (2863449228129/1000000000000 : ℝ)*(major_s1_0) + (2863449228129/1000000000000 : ℝ)*(major_s1_1) + (2863449228129/1000000000000 : ℝ)*(major_s1_2) + (10613129/1000000000000 : ℝ)*(sp_s1_0) + (13789069/1000000000000 : ℝ)*(sp_s1_1) + (3724537090103/1000000000000 : ℝ)*(sp_s1_7) + (29098664199/7812500000 : ℝ)*(sp_s1_8) + (931161062233/250000000000 : ℝ)*(sp_s1_9) + (2241342855949/1000000000000 : ℝ)*(sp_s1_13) + (96545701/1000000000000 : ℝ)*(sp_s1_14) + (1442391/1000000000000 : ℝ)*(sp_s1_22) + (832064238221/500000000000 : ℝ)*(f.failure) + (931161062233/250000000000 : ℝ)*(f.sum) + (4070881035808921493/10557803300000000000000000000000 : ℝ)*base63 + (1805688810643031/2346700000000000000000000000 : ℝ)*base64 + (276433560469091/539880000000000000000000000 : ℝ)*base67 + (974181421043979/2346700000000000000000000000 : ℝ)*base69 + (32247719112985278253/95860348300000000000000000000000 : ℝ)*base70 + (1592127225160013/8169800000000000000000000000 : ℝ)*base73 + (1573414652603/224950000000000000000000000 : ℝ)*base75 + (324712991985239/2042450000000000000000000000 : ℝ)*base77 + (2093789849011297411/6891736912500000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base81 + (751/50000000000000000 : ℝ)*base86 + (751/50000000000000000 : ℝ)*base88 + (751/50000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59533/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(59533/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (158534296398428878392855558687/43127570700170000000000000000000000 : ℝ) := by norm_num
    linear_combination (596178752263/1000000000000 : ℝ)*(base7) + (2767930181151/1000000000000 : ℝ)*(major_s1_0) + (2767930181151/1000000000000 : ℝ)*(major_s1_1) + (2767930181151/1000000000000 : ℝ)*(major_s1_2) + (26663/500000000000 : ℝ)*(sp_s1_0) + (253199/1000000000000 : ℝ)*(sp_s1_1) + (1407307/1000000000000 : ℝ)*(sp_s1_2) + (736377/500000000000 : ℝ)*(sp_s1_7) + (22129477/1000000000000 : ℝ)*(sp_s1_8) + (3578011605223/1000000000000 : ℝ)*(sp_s1_14) + (3577990748627/1000000000000 : ℝ)*(sp_s1_15) + (894502930999/250000000000 : ℝ)*(sp_s1_16) + (1102392742737/500000000000 : ℝ)*(sp_s1_20) + (1936593/200000000000 : ℝ)*(sp_s1_27) + (100538526011/62500000000 : ℝ)*(f.failure) + (3578013131303/1000000000000 : ℝ)*(f.sum) + (2853022905484250397/10557803300000000000000000000000 : ℝ)*base63 + (1186391843685911/2346700000000000000000000000 : ℝ)*base65 + (272081915748427/539880000000000000000000000 : ℝ)*base66 + (1525098429731231/2346700000000000000000000000 : ℝ)*base69 + (11021124736955650923/95860348300000000000000000000000 : ℝ)*base71 + (4216788630371493/8169800000000000000000000000 : ℝ)*base72 + (81491132284271/112475000000000000000000000 : ℝ)*base75 + (1202732307425771/2042450000000000000000000000 : ℝ)*base77 + (2438597239501073401/27566947650000000000000000000000 : ℝ)*base79 + (6991/6250000000000000 : ℝ)*base86 + (6991/6250000000000000 : ℝ)*base88 + (6991/6250000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s1_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-44133/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-44133/100000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10861233511216977711003/2042450000000000000000000000 : ℝ) := by norm_num
    linear_combination (204148529539/1000000000000 : ℝ)*(base7) + (99369/15625000000 : ℝ)*(base11) + (265553201423/1000000000000 : ℝ)*(base39) + (185873/1000000000000 : ℝ)*(base59) + (90727106027/31250000000 : ℝ)*(major_s1_0) + (90727106027/31250000000 : ℝ)*(major_s1_1) + (90727106027/31250000000 : ℝ)*(major_s1_2) + (11541487/1000000000000 : ℝ)*(sp_s1_0) + (2399183/250000000000 : ℝ)*(sp_s1_2) + (9115321/250000000000 : ℝ)*(sp_s1_9) + (499957462177/125000000000 : ℝ)*(sp_s1_21) + (99991939963/25000000000 : ℝ)*(sp_s1_22) + (3999631540503/1000000000000 : ℝ)*(sp_s1_23) + (472854454631/250000000000 : ℝ)*(sp_s1_27) + (337453857797/200000000000 : ℝ)*(f.failure) + (99991939963/25000000000 : ℝ)*(f.sum) + (332361179374475841/5278901650000000000000000000000 : ℝ)*base62 + (431726080078471/586675000000000000000000000 : ℝ)*base65 + (50625658524989/101227500000000000000000000 : ℝ)*base66 + (2967963863329/55000781250000000000000000 : ℝ)*base69 + (546497874511858121/11982543537500000000000000000000 : ℝ)*base70 + (4912957056337/127653125000000000000000000 : ℝ)*base73 + (419379678351769/674850000000000000000000000 : ℝ)*base75 + (756343966235657/1021225000000000000000000000 : ℝ)*base77 + (26675394141934421387/82700842950000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base84 + (8007/20000000000000000 : ℝ)*base86 + (8007/20000000000000000 : ℝ)*base88 + (8007/20000000000000000 : ℝ)*base90 + hcertificate_margin
  exact ⟨ratio_s1_0,ratio_s1_1,ratio_s1_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (37/8 : ℝ) ≤ p) (hpb : p ≤ (75/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (172069/100000 : ℝ) (87867/50000 : ℝ) (15771/20000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, false]])
    (hprev0 : (0 : ℝ) ≤ ((40849/50000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(40849/50000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(40491/50000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(40491/50000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-70401/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-70401/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((2373/4000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(2373/4000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(59533/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(59533/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(-44133/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(-44133/100000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c314062_s1 p hpa hpb X hX hprev0

#print axioms solution
