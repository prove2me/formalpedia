-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.collision_c312063_s3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:20:58.917787+00:00
-- url     : https://prove2.me/submissions/0708f02c-5162-41cf-815d-ffc7369f9856

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
theorem collision_support_c312063_s3_s3_0 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1477161521/10000000000 : ℝ)*x 0 + (5407166697/10000000000 : ℝ)*x 1 + (5440915607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1477161521/10000000000 : ℝ)^73 ≤ (1727089962997/20000000000000 : ℝ)^57 := by
    have hnat : (1477161521 : ℕ)^73*20000000000000^57 ≤ 1727089962997^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1477161521 10000000000 1727089962997 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407166697/10000000000 : ℝ)^73 ≤ (22750131206723/50000000000000 : ℝ)^57 := by
    have hnat : (5407166697 : ℕ)^73*50000000000000^57 ≤ 22750131206723^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407166697 10000000000 22750131206723 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5440915607/10000000000 : ℝ)^73 ≤ (45864287745803/100000000000000 : ℝ)^57 := by
    have hnat : (5440915607 : ℕ)^73*100000000000000^57 ≤ 45864287745803^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5440915607 10000000000 45864287745803 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1477161521/10000000000 : ℝ), (5407166697/10000000000 : ℝ), (5440915607/10000000000 : ℝ)] ![(1727089962997/20000000000000 : ℝ), (22750131206723/50000000000000 : ℝ), (45864287745803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1477161521/10000000000 : ℝ)|^73 ≤ (1727089962997/20000000000000 : ℝ)^57
        have hw : |(-1477161521/10000000000 : ℝ)|=(1477161521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407166697/10000000000 : ℝ)|^73 ≤ (22750131206723/50000000000000 : ℝ)^57
        have hw : |(5407166697/10000000000 : ℝ)|=(5407166697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5440915607/10000000000 : ℝ)|^73 ≤ (45864287745803/100000000000000 : ℝ)^57
        have hw : |(5440915607/10000000000 : ℝ)|=(5440915607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s3_s3_1 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2704163929/5000000000 : ℝ)*x 0 + (-1487602769/10000000000 : ℝ)*x 1 + (1086501261/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2704163929/5000000000 : ℝ)^73 ≤ (22756388228707/50000000000000 : ℝ)^57 := by
    have hnat : (2704163929 : ℕ)^73*50000000000000^57 ≤ 22756388228707^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2704163929 5000000000 22756388228707 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1487602769/10000000000 : ℝ)^73 ≤ (8713700347403/100000000000000 : ℝ)^57 := by
    have hnat : (1487602769 : ℕ)^73*100000000000000^57 ≤ 8713700347403^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1487602769 10000000000 8713700347403 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1086501261/2000000000 : ℝ)^73 ≤ (5721690396713/12500000000000 : ℝ)^57 := by
    have hnat : (1086501261 : ℕ)^73*12500000000000^57 ≤ 5721690396713^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086501261 2000000000 5721690396713 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2704163929/5000000000 : ℝ), (-1487602769/10000000000 : ℝ), (1086501261/2000000000 : ℝ)] ![(22756388228707/50000000000000 : ℝ), (8713700347403/100000000000000 : ℝ), (5721690396713/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2704163929/5000000000 : ℝ)|^73 ≤ (22756388228707/50000000000000 : ℝ)^57
        have hw : |(2704163929/5000000000 : ℝ)|=(2704163929/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1487602769/10000000000 : ℝ)|^73 ≤ (8713700347403/100000000000000 : ℝ)^57
        have hw : |(-1487602769/10000000000 : ℝ)|=(1487602769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1086501261/2000000000 : ℝ)|^73 ≤ (5721690396713/12500000000000 : ℝ)^57
        have hw : |(1086501261/2000000000 : ℝ)|=(1086501261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s3_s3_2 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2716152413/5000000000 : ℝ)*x 0 + (678412439/1250000000 : ℝ)*x 1 + (-146055399/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2716152413/5000000000 : ℝ)^73 ≤ (45771349023059/100000000000000 : ℝ)^57 := by
    have hnat : (2716152413 : ℕ)^73*100000000000000^57 ≤ 45771349023059^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2716152413 5000000000 45771349023059 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678412439/1250000000 : ℝ)^73 ≤ (5714668022099/12500000000000 : ℝ)^57 := by
    have hnat : (678412439 : ℕ)^73*12500000000000^57 ≤ 5714668022099^57*1250000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678412439 1250000000 5714668022099 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (146055399/1000000000 : ℝ)^73 ≤ (4255653389667/50000000000000 : ℝ)^57 := by
    have hnat : (146055399 : ℕ)^73*50000000000000^57 ≤ 4255653389667^57*1000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146055399 1000000000 4255653389667 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2716152413/5000000000 : ℝ), (678412439/1250000000 : ℝ), (-146055399/1000000000 : ℝ)] ![(45771349023059/100000000000000 : ℝ), (5714668022099/12500000000000 : ℝ), (4255653389667/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2716152413/5000000000 : ℝ)|^73 ≤ (45771349023059/100000000000000 : ℝ)^57
        have hw : |(2716152413/5000000000 : ℝ)|=(2716152413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678412439/1250000000 : ℝ)|^73 ≤ (5714668022099/12500000000000 : ℝ)^57
        have hw : |(678412439/1250000000 : ℝ)|=(678412439/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-146055399/1000000000 : ℝ)|^73 ≤ (4255653389667/50000000000000 : ℝ)^57
        have hw : |(-146055399/1000000000 : ℝ)|=(146055399/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s3_s3_6 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2128485407/5000000000 : ℝ)*x 0 + (1061714023/2500000000 : ℝ)*x 1 + (2109353733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2128485407/5000000000 : ℝ)^73 ≤ (33495663176379/100000000000000 : ℝ)^57 := by
    have hnat : (2128485407 : ℕ)^73*100000000000000^57 ≤ 33495663176379^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128485407 5000000000 33495663176379 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061714023/2500000000 : ℝ)^73 ≤ (33393770040457/100000000000000 : ℝ)^57 := by
    have hnat : (1061714023 : ℕ)^73*100000000000000^57 ≤ 33393770040457^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061714023 2500000000 33393770040457 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2109353733/5000000000 : ℝ)^73 ≤ (33110566764443/100000000000000 : ℝ)^57 := by
    have hnat : (2109353733 : ℕ)^73*100000000000000^57 ≤ 33110566764443^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109353733 5000000000 33110566764443 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2128485407/5000000000 : ℝ), (1061714023/2500000000 : ℝ), (2109353733/5000000000 : ℝ)] ![(33495663176379/100000000000000 : ℝ), (33393770040457/100000000000000 : ℝ), (33110566764443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2128485407/5000000000 : ℝ)|^73 ≤ (33495663176379/100000000000000 : ℝ)^57
        have hw : |(2128485407/5000000000 : ℝ)|=(2128485407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1061714023/2500000000 : ℝ)|^73 ≤ (33393770040457/100000000000000 : ℝ)^57
        have hw : |(1061714023/2500000000 : ℝ)|=(1061714023/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2109353733/5000000000 : ℝ)|^73 ≤ (33110566764443/100000000000000 : ℝ)^57
        have hw : |(2109353733/5000000000 : ℝ)|=(2109353733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s3_s3_7 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-1332858289/10000000000 : ℝ)*x 0 + (911641043/2000000000 : ℝ)*x 1 + (6347237739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1332858289/10000000000 : ℝ)^73 ≤ (151404680047/2000000000000 : ℝ)^57 := by
    have hnat : (1332858289 : ℕ)^73*2000000000000^57 ≤ 151404680047^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1332858289 10000000000 151404680047 2000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (911641043/2000000000 : ℝ)^73 ≤ (18280443155913/50000000000000 : ℝ)^57 := by
    have hnat : (911641043 : ℕ)^73*50000000000000^57 ≤ 18280443155913^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      911641043 2000000000 18280443155913 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6347237739/10000000000 : ℝ)^73 ≤ (55868879672387/100000000000000 : ℝ)^57 := by
    have hnat : (6347237739 : ℕ)^73*100000000000000^57 ≤ 55868879672387^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6347237739 10000000000 55868879672387 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1332858289/10000000000 : ℝ), (911641043/2000000000 : ℝ), (6347237739/10000000000 : ℝ)] ![(151404680047/2000000000000 : ℝ), (18280443155913/50000000000000 : ℝ), (55868879672387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1332858289/10000000000 : ℝ)|^73 ≤ (151404680047/2000000000000 : ℝ)^57
        have hw : |(-1332858289/10000000000 : ℝ)|=(1332858289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(911641043/2000000000 : ℝ)|^73 ≤ (18280443155913/50000000000000 : ℝ)^57
        have hw : |(911641043/2000000000 : ℝ)|=(911641043/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6347237739/10000000000 : ℝ)|^73 ≤ (55868879672387/100000000000000 : ℝ)^57
        have hw : |(6347237739/10000000000 : ℝ)|=(6347237739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s3_s3_8 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4991378457/10000000000 : ℝ)*x 0 + (-336755161/5000000000 : ℝ)*x 1 + (316936581/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4991378457/10000000000 : ℝ)^73 ≤ (1026716340269/2500000000000 : ℝ)^57 := by
    have hnat : (4991378457 : ℕ)^73*2500000000000^57 ≤ 1026716340269^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4991378457 10000000000 1026716340269 2500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (336755161/5000000000 : ℝ)^73 ≤ (3158336745213/100000000000000 : ℝ)^57 := by
    have hnat : (336755161 : ℕ)^73*100000000000000^57 ≤ 3158336745213^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336755161 5000000000 3158336745213 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (316936581/500000000 : ℝ)^73 ≤ (1394325240657/2500000000000 : ℝ)^57 := by
    have hnat : (316936581 : ℕ)^73*2500000000000^57 ≤ 1394325240657^57*500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      316936581 500000000 1394325240657 2500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4991378457/10000000000 : ℝ), (-336755161/5000000000 : ℝ), (316936581/500000000 : ℝ)] ![(1026716340269/2500000000000 : ℝ), (3158336745213/100000000000000 : ℝ), (1394325240657/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4991378457/10000000000 : ℝ)|^73 ≤ (1026716340269/2500000000000 : ℝ)^57
        have hw : |(4991378457/10000000000 : ℝ)|=(4991378457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-336755161/5000000000 : ℝ)|^73 ≤ (3158336745213/100000000000000 : ℝ)^57
        have hw : |(-336755161/5000000000 : ℝ)|=(336755161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(316936581/500000000 : ℝ)|^73 ≤ (1394325240657/2500000000000 : ℝ)^57
        have hw : |(316936581/500000000 : ℝ)|=(316936581/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s3_s3_9 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2380825951/5000000000 : ℝ)*x 0 + (6573015857/10000000000 : ℝ)*x 1 + (-315865357/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2380825951/5000000000 : ℝ)^73 ≤ (19331860512281/50000000000000 : ℝ)^57 := by
    have hnat : (2380825951 : ℕ)^73*50000000000000^57 ≤ 19331860512281^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2380825951 5000000000 19331860512281 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6573015857/10000000000 : ℝ)^73 ≤ (58426639238197/100000000000000 : ℝ)^57 := by
    have hnat : (6573015857 : ℕ)^73*100000000000000^57 ≤ 58426639238197^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6573015857 10000000000 58426639238197 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (315865357/5000000000 : ℝ)^73 ≤ (2909639729923/100000000000000 : ℝ)^57 := by
    have hnat : (315865357 : ℕ)^73*100000000000000^57 ≤ 2909639729923^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      315865357 5000000000 2909639729923 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2380825951/5000000000 : ℝ), (6573015857/10000000000 : ℝ), (-315865357/5000000000 : ℝ)] ![(19331860512281/50000000000000 : ℝ), (58426639238197/100000000000000 : ℝ), (2909639729923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2380825951/5000000000 : ℝ)|^73 ≤ (19331860512281/50000000000000 : ℝ)^57
        have hw : |(2380825951/5000000000 : ℝ)|=(2380825951/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6573015857/10000000000 : ℝ)|^73 ≤ (58426639238197/100000000000000 : ℝ)^57
        have hw : |(6573015857/10000000000 : ℝ)|=(6573015857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-315865357/5000000000 : ℝ)|^73 ≤ (2909639729923/100000000000000 : ℝ)^57
        have hw : |(-315865357/5000000000 : ℝ)|=(315865357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s3_s3_13 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (2237311263/5000000000 : ℝ)*x 0 + (5780068387/10000000000 : ℝ)*x 1 + (2242354053/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2237311263/5000000000 : ℝ)^73 ≤ (35704513073319/100000000000000 : ℝ)^57 := by
    have hnat : (2237311263 : ℕ)^73*100000000000000^57 ≤ 35704513073319^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237311263 5000000000 35704513073319 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5780068387/10000000000 : ℝ)^73 ≤ (24778621974467/50000000000000 : ℝ)^57 := by
    have hnat : (5780068387 : ℕ)^73*50000000000000^57 ≤ 24778621974467^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5780068387 10000000000 24778621974467 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2242354053/10000000000 : ℝ)^73 ≤ (1842280370869/12500000000000 : ℝ)^57 := by
    have hnat : (2242354053 : ℕ)^73*12500000000000^57 ≤ 1842280370869^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242354053 10000000000 1842280370869 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2237311263/5000000000 : ℝ), (5780068387/10000000000 : ℝ), (2242354053/10000000000 : ℝ)] ![(35704513073319/100000000000000 : ℝ), (24778621974467/50000000000000 : ℝ), (1842280370869/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2237311263/5000000000 : ℝ)|^73 ≤ (35704513073319/100000000000000 : ℝ)^57
        have hw : |(2237311263/5000000000 : ℝ)|=(2237311263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5780068387/10000000000 : ℝ)|^73 ≤ (24778621974467/50000000000000 : ℝ)^57
        have hw : |(5780068387/10000000000 : ℝ)|=(5780068387/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2242354053/10000000000 : ℝ)|^73 ≤ (1842280370869/12500000000000 : ℝ)^57
        have hw : |(2242354053/10000000000 : ℝ)|=(2242354053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s3_s3_14 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-661783147/10000000000 : ℝ)*x 0 + (2501043187/5000000000 : ℝ)*x 1 + (1583737457/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661783147/10000000000 : ℝ)^73 ≤ (3088079925339/100000000000000 : ℝ)^57 := by
    have hnat : (661783147 : ℕ)^73*100000000000000^57 ≤ 3088079925339^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661783147 10000000000 3088079925339 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2501043187/5000000000 : ℝ)^73 ≤ (8236304468313/20000000000000 : ℝ)^57 := by
    have hnat : (2501043187 : ℕ)^73*20000000000000^57 ≤ 8236304468313^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2501043187 5000000000 8236304468313 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1583737457/2500000000 : ℝ)^73 ≤ (55730397717673/100000000000000 : ℝ)^57 := by
    have hnat : (1583737457 : ℕ)^73*100000000000000^57 ≤ 55730397717673^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1583737457 2500000000 55730397717673 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-661783147/10000000000 : ℝ), (2501043187/5000000000 : ℝ), (1583737457/2500000000 : ℝ)] ![(3088079925339/100000000000000 : ℝ), (8236304468313/20000000000000 : ℝ), (55730397717673/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-661783147/10000000000 : ℝ)|^73 ≤ (3088079925339/100000000000000 : ℝ)^57
        have hw : |(-661783147/10000000000 : ℝ)|=(661783147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2501043187/5000000000 : ℝ)|^73 ≤ (8236304468313/20000000000000 : ℝ)^57
        have hw : |(2501043187/5000000000 : ℝ)|=(2501043187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1583737457/2500000000 : ℝ)|^73 ≤ (55730397717673/100000000000000 : ℝ)^57
        have hw : |(1583737457/2500000000 : ℝ)|=(1583737457/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s3_s3_15 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4582799129/10000000000 : ℝ)*x 0 + (-1330309221/10000000000 : ℝ)*x 1 + (3163222201/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4582799129/10000000000 : ℝ)^73 ≤ (4601714409429/12500000000000 : ℝ)^57 := by
    have hnat : (4582799129 : ℕ)^73*12500000000000^57 ≤ 4601714409429^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4582799129 10000000000 4601714409429 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1330309221/10000000000 : ℝ)^73 ≤ (7551697059519/100000000000000 : ℝ)^57 := by
    have hnat : (1330309221 : ℕ)^73*100000000000000^57 ≤ 7551697059519^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1330309221 10000000000 7551697059519 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3163222201/5000000000 : ℝ)^73 ≤ (55634587645787/100000000000000 : ℝ)^57 := by
    have hnat : (3163222201 : ℕ)^73*100000000000000^57 ≤ 55634587645787^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3163222201 5000000000 55634587645787 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4582799129/10000000000 : ℝ), (-1330309221/10000000000 : ℝ), (3163222201/5000000000 : ℝ)] ![(4601714409429/12500000000000 : ℝ), (7551697059519/100000000000000 : ℝ), (55634587645787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4582799129/10000000000 : ℝ)|^73 ≤ (4601714409429/12500000000000 : ℝ)^57
        have hw : |(4582799129/10000000000 : ℝ)|=(4582799129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1330309221/10000000000 : ℝ)|^73 ≤ (7551697059519/100000000000000 : ℝ)^57
        have hw : |(-1330309221/10000000000 : ℝ)|=(1330309221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3163222201/5000000000 : ℝ)|^73 ≤ (55634587645787/100000000000000 : ℝ)^57
        have hw : |(3163222201/5000000000 : ℝ)|=(3163222201/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s3_s3_16 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (1265054231/2000000000 : ℝ)*x 0 + (1255611337/2500000000 : ℝ)*x 1 + (-644018559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1265054231/2000000000 : ℝ)^73 ≤ (55621374344737/100000000000000 : ℝ)^57 := by
    have hnat : (1265054231 : ℕ)^73*100000000000000^57 ≤ 55621374344737^57*2000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1265054231 2000000000 55621374344737 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1255611337/2500000000 : ℝ)^73 ≤ (10349076702979/25000000000000 : ℝ)^57 := by
    have hnat : (1255611337 : ℕ)^73*25000000000000^57 ≤ 10349076702979^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255611337 2500000000 10349076702979 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (644018559/10000000000 : ℝ)^73 ≤ (2982318820487/100000000000000 : ℝ)^57 := by
    have hnat : (644018559 : ℕ)^73*100000000000000^57 ≤ 2982318820487^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      644018559 10000000000 2982318820487 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1265054231/2000000000 : ℝ), (1255611337/2500000000 : ℝ), (-644018559/10000000000 : ℝ)] ![(55621374344737/100000000000000 : ℝ), (10349076702979/25000000000000 : ℝ), (2982318820487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1265054231/2000000000 : ℝ)|^73 ≤ (55621374344737/100000000000000 : ℝ)^57
        have hw : |(1265054231/2000000000 : ℝ)|=(1265054231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1255611337/2500000000 : ℝ)|^73 ≤ (10349076702979/25000000000000 : ℝ)^57
        have hw : |(1255611337/2500000000 : ℝ)|=(1255611337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-644018559/10000000000 : ℝ)|^73 ≤ (2982318820487/100000000000000 : ℝ)^57
        have hw : |(-644018559/10000000000 : ℝ)|=(644018559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s3_s3_20 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6329273623/10000000000 : ℝ)*x 0 + (1920001503/5000000000 : ℝ)*x 1 + (141942881/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6329273623/10000000000 : ℝ)^73 ≤ (2783322681403/5000000000000 : ℝ)^57 := by
    have hnat : (6329273623 : ℕ)^73*5000000000000^57 ≤ 2783322681403^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6329273623 10000000000 2783322681403 5000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1920001503/5000000000 : ℝ)^73 ≤ (29353014236129/100000000000000 : ℝ)^57 := by
    have hnat : (1920001503 : ℕ)^73*100000000000000^57 ≤ 29353014236129^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1920001503 5000000000 29353014236129 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (141942881/625000000 : ℝ)^73 ≤ (7490266060571/50000000000000 : ℝ)^57 := by
    have hnat : (141942881 : ℕ)^73*50000000000000^57 ≤ 7490266060571^57*625000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141942881 625000000 7490266060571 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6329273623/10000000000 : ℝ), (1920001503/5000000000 : ℝ), (141942881/625000000 : ℝ)] ![(2783322681403/5000000000000 : ℝ), (29353014236129/100000000000000 : ℝ), (7490266060571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6329273623/10000000000 : ℝ)|^73 ≤ (2783322681403/5000000000000 : ℝ)^57
        have hw : |(6329273623/10000000000 : ℝ)|=(6329273623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1920001503/5000000000 : ℝ)|^73 ≤ (29353014236129/100000000000000 : ℝ)^57
        have hw : |(1920001503/5000000000 : ℝ)|=(1920001503/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(141942881/625000000 : ℝ)|^73 ≤ (7490266060571/50000000000000 : ℝ)^57
        have hw : |(141942881/625000000 : ℝ)|=(141942881/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s3_s3_21 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (-602669483/10000000000 : ℝ)*x 0 + (5970358569/10000000000 : ℝ)*x 1 + (1354205887/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (602669483/10000000000 : ℝ)^73 ≤ (684833980183/25000000000000 : ℝ)^57 := by
    have hnat : (602669483 : ℕ)^73*25000000000000^57 ≤ 684833980183^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      602669483 10000000000 684833980183 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5970358569/10000000000 : ℝ)^73 ≤ (6457038134951/12500000000000 : ℝ)^57 := by
    have hnat : (5970358569 : ℕ)^73*12500000000000^57 ≤ 6457038134951^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5970358569 10000000000 6457038134951 12500000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1354205887/2500000000 : ℝ)^73 ≤ (45604358997129/100000000000000 : ℝ)^57 := by
    have hnat : (1354205887 : ℕ)^73*100000000000000^57 ≤ 45604358997129^57*2500000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1354205887 2500000000 45604358997129 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-602669483/10000000000 : ℝ), (5970358569/10000000000 : ℝ), (1354205887/2500000000 : ℝ)] ![(684833980183/25000000000000 : ℝ), (6457038134951/12500000000000 : ℝ), (45604358997129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-602669483/10000000000 : ℝ)|^73 ≤ (684833980183/25000000000000 : ℝ)^57
        have hw : |(-602669483/10000000000 : ℝ)|=(602669483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5970358569/10000000000 : ℝ)|^73 ≤ (6457038134951/12500000000000 : ℝ)^57
        have hw : |(5970358569/10000000000 : ℝ)|=(5970358569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1354205887/2500000000 : ℝ)|^73 ≤ (45604358997129/100000000000000 : ℝ)^57
        have hw : |(1354205887/2500000000 : ℝ)|=(1354205887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s3_s3_22 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (6360137219/10000000000 : ℝ)*x 0 + (-301037737/5000000000 : ℝ)*x 1 + (2504279759/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6360137219/10000000000 : ℝ)^73 ≤ (56014334856103/100000000000000 : ℝ)^57 := by
    have hnat : (6360137219 : ℕ)^73*100000000000000^57 ≤ 56014334856103^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6360137219 10000000000 56014334856103 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (301037737/5000000000 : ℝ)^73 ≤ (2735878541451/100000000000000 : ℝ)^57 := by
    have hnat : (301037737 : ℕ)^73*100000000000000^57 ≤ 2735878541451^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      301037737 5000000000 2735878541451 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2504279759/5000000000 : ℝ)^73 ≤ (2062489329639/5000000000000 : ℝ)^57 := by
    have hnat : (2504279759 : ℕ)^73*5000000000000^57 ≤ 2062489329639^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2504279759 5000000000 2062489329639 5000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6360137219/10000000000 : ℝ), (-301037737/5000000000 : ℝ), (2504279759/5000000000 : ℝ)] ![(56014334856103/100000000000000 : ℝ), (2735878541451/100000000000000 : ℝ), (2062489329639/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6360137219/10000000000 : ℝ)|^73 ≤ (56014334856103/100000000000000 : ℝ)^57
        have hw : |(6360137219/10000000000 : ℝ)|=(6360137219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-301037737/5000000000 : ℝ)|^73 ≤ (2735878541451/100000000000000 : ℝ)^57
        have hw : |(-301037737/5000000000 : ℝ)|=(301037737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2504279759/5000000000 : ℝ)|^73 ≤ (2062489329639/5000000000000 : ℝ)^57
        have hw : |(2504279759/5000000000 : ℝ)|=(2504279759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s3_s3_23 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (4531669757/10000000000 : ℝ)*x 0 + (6390478873/10000000000 : ℝ)*x 1 + (-1303130913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4531669757/10000000000 : ℝ)^73 ≤ (36288527172903/100000000000000 : ℝ)^57 := by
    have hnat : (4531669757 : ℕ)^73*100000000000000^57 ≤ 36288527172903^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4531669757 10000000000 36288527172903 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6390478873/10000000000 : ℝ)^73 ≤ (56356795216881/100000000000000 : ℝ)^57 := by
    have hnat : (6390478873 : ℕ)^73*100000000000000^57 ≤ 56356795216881^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6390478873 10000000000 56356795216881 100000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1303130913/10000000000 : ℝ)^73 ≤ (294187103849/4000000000000 : ℝ)^57 := by
    have hnat : (1303130913 : ℕ)^73*4000000000000^57 ≤ 294187103849^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1303130913 10000000000 294187103849 4000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4531669757/10000000000 : ℝ), (6390478873/10000000000 : ℝ), (-1303130913/10000000000 : ℝ)] ![(36288527172903/100000000000000 : ℝ), (56356795216881/100000000000000 : ℝ), (294187103849/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4531669757/10000000000 : ℝ)|^73 ≤ (36288527172903/100000000000000 : ℝ)^57
        have hw : |(4531669757/10000000000 : ℝ)|=(4531669757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6390478873/10000000000 : ℝ)|^73 ≤ (56356795216881/100000000000000 : ℝ)^57
        have hw : |(6390478873/10000000000 : ℝ)|=(6390478873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1303130913/10000000000 : ℝ)|^73 ≤ (294187103849/4000000000000 : ℝ)^57
        have hw : |(-1303130913/10000000000 : ℝ)|=(1303130913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_support_c312063_s3_s3_27 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ)) (x : Fin 3 → ℝ) :
    (3252759663/5000000000 : ℝ)*x 0 + (3071944951/10000000000 : ℝ)*x 1 + (5620159/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3252759663/5000000000 : ℝ)^73 ≤ (14414842509393/25000000000000 : ℝ)^57 := by
    have hnat : (3252759663 : ℕ)^73*25000000000000^57 ≤ 14414842509393^57*5000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3252759663 5000000000 14414842509393 25000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3071944951/10000000000 : ℝ)^73 ≤ (11028069222047/50000000000000 : ℝ)^57 := by
    have hnat : (3071944951 : ℕ)^73*50000000000000^57 ≤ 11028069222047^57*10000000000^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3071944951 10000000000 11028069222047 50000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5620159/19531250 : ℝ)^73 ≤ (4056898298961/20000000000000 : ℝ)^57 := by
    have hnat : (5620159 : ℕ)^73*20000000000000^57 ≤ 4056898298961^57*19531250^73 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5620159 19531250 4056898298961 20000000000000 73 57 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (73/16 : ℝ)) 73 57 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3252759663/5000000000 : ℝ), (3071944951/10000000000 : ℝ), (5620159/19531250 : ℝ)] ![(14414842509393/25000000000000 : ℝ), (11028069222047/50000000000000 : ℝ), (4056898298961/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3252759663/5000000000 : ℝ)|^73 ≤ (14414842509393/25000000000000 : ℝ)^57
        have hw : |(3252759663/5000000000 : ℝ)|=(3252759663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3071944951/10000000000 : ℝ)|^73 ≤ (11028069222047/50000000000000 : ℝ)^57
        have hw : |(3071944951/10000000000 : ℝ)|=(3071944951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5620159/19531250 : ℝ)|^73 ≤ (4056898298961/20000000000000 : ℝ)^57
        have hw : |(5620159/19531250 : ℝ)|=(5620159/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem collision_c312063_s3 (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((6601/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6601/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13417/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13417/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(51377/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(51377/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3669/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3669/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37237/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(37237/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17779/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(17779/50000 : ℝ)*X 1 2) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : RawLinearData _ _ X N P T := raw_linear_data (by linarith : (1 : ℝ) ≤ p) X hX.raw
  have bounds := raw_linear_data_bounds f (by norm_num)
  have main0 : (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.main 0
    change (78337/100000 : ℝ)*P 0 ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order0 : 0 ≤ ((1 : ℝ)*(X 1 2+X 2 2)) ∧ ((1 : ℝ)*(X 1 2+X 2 2)) ≤ ((1 : ℝ)*(X 1 1+X 2 1)) ∧ ((1 : ℝ)*(X 1 1+X 2 1)) ≤ ((1 : ℝ)*(X 1 0+X 2 0)) := by
    have hh := hX.ordered 0
    change 0 ≤ ((1 : ℝ)*pair X 0 2) ∧ ((1 : ℝ)*pair X 0 2) ≤ ((1 : ℝ)*pair X 0 1) ∧ ((1 : ℝ)*pair X 0 1) ≤ ((1 : ℝ)*pair X 0 0) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main1 : (78337/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.main 1
    change (78337/100000 : ℝ)*P 1 ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have order1 : 0 ≤ ((1 : ℝ)*(X 0 2+X 2 2)) ∧ ((1 : ℝ)*(X 0 2+X 2 2)) ≤ ((1 : ℝ)*(X 0 0+X 2 0)) ∧ ((1 : ℝ)*(X 0 0+X 2 0)) ≤ ((1 : ℝ)*(X 0 1+X 2 1)) := by
    have hh := hX.ordered 1
    change 0 ≤ ((1 : ℝ)*pair X 1 2) ∧ ((1 : ℝ)*pair X 1 2) ≤ ((1 : ℝ)*pair X 1 0) ∧ ((1 : ℝ)*pair X 1 0) ≤ ((1 : ℝ)*pair X 1 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have main2 : (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2)) := by
    have hh := hX.main 2
    change (78337/100000 : ℝ)*P 2 ≤ ((1 : ℝ)*pair X 2 2) at hh
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
  rcases hprev2 with ⟨ratio_s2_0,ratio_s2_1,ratio_s2_2⟩
  have s3_pow0 : (6601/12500 : ℝ) ^ (9/2 : ℝ) ≤ (113026097947601757/2000000000000000000 : ℝ) := by
    have hpowers : (6601/12500 : ℝ)^9 ≤ (113026097947601757/2000000000000000000 : ℝ)^2 := by
      have hnat : (6601 : ℕ)^9*2000000000000000000^2 ≤ 113026097947601757^2*12500^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6601 12500 113026097947601757 2000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6601/12500 : ℝ)) (X := (113026097947601757/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s3_corner0a : (2113026097947601757/2000000000000000000 : ℝ) ≤ (10122913495579717/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (2113026097947601757/2000000000000000000 : ℝ)^2 ≤ (10122913495579717/10000000000000000 : ℝ)^9 := by
      have hnat : (2113026097947601757 : ℕ)^2*10000000000000000^9 ≤ 10122913495579717^9*2000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2113026097947601757 2000000000000000000 10122913495579717 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10122913495579717/10000000000000000 : ℝ)) (X := (2113026097947601757/2000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s3_corner0b : (1113026097947601757/1000000000000000000 : ℝ) ≤ (2560203755966081/2500000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (1113026097947601757/1000000000000000000 : ℝ)^2 ≤ (2560203755966081/2500000000000000 : ℝ)^9 := by
      have hnat : (1113026097947601757 : ℕ)^2*2500000000000000^9 ≤ 2560203755966081^9*1000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1113026097947601757 1000000000000000000 2560203755966081 2500000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2560203755966081/2500000000000000 : ℝ)) (X := (1113026097947601757/1000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s3_0 : P 0 ≤ ((1 : ℝ)*(X 1 0+X 2 0))+(122913495579717/5280800000000000 : ℝ)*((1 : ℝ)*(X 1 1+X 2 1))+(117901528284607/5280800000000000 : ℝ)*((1 : ℝ)*(X 1 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (6601/12500 : ℝ)) (alpha := (122913495579717/5280800000000000 : ℝ)) (beta := (117901528284607/5280800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow0,s3_corner0a]) (by linarith only [s3_pow0,s3_corner0b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 0 (by
        change ((1 : ℝ)*pair X 0 1) ≤ (6601/12500 : ℝ)*((1 : ℝ)*pair X 0 0)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_0])
    change lpNorm p (pair X 0) ≤ ((1 : ℝ)*pair X 0 0)+(122913495579717/5280800000000000 : ℝ)*((1 : ℝ)*pair X 0 1)+(117901528284607/5280800000000000 : ℝ)*((1 : ℝ)*pair X 0 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow1 : (13417/25000 : ℝ) ^ (9/2 : ℝ) ≤ (759677673589724701/12500000000000000000 : ℝ) := by
    have hpowers : (13417/25000 : ℝ)^9 ≤ (759677673589724701/12500000000000000000 : ℝ)^2 := by
      have hnat : (13417 : ℕ)^9*12500000000000000000^2 ≤ 759677673589724701^2*25000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13417 25000 759677673589724701 12500000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13417/25000 : ℝ)) (X := (759677673589724701/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s3_corner1a : (13259677673589724701/12500000000000000000 : ℝ) ≤ (5065986103220093/5000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (13259677673589724701/12500000000000000000 : ℝ)^2 ≤ (5065986103220093/5000000000000000 : ℝ)^9 := by
      have hnat : (13259677673589724701 : ℕ)^2*5000000000000000^9 ≤ 5065986103220093^9*12500000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13259677673589724701 12500000000000000000 5065986103220093 5000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5065986103220093/5000000000000000 : ℝ)) (X := (13259677673589724701/12500000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s3_corner1b : (7009677673589724701/6250000000000000000 : ℝ) ≤ (2051637692076741/2000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (7009677673589724701/6250000000000000000 : ℝ)^2 ≤ (2051637692076741/2000000000000000 : ℝ)^9 := by
      have hnat : (7009677673589724701 : ℕ)^2*2000000000000000^9 ≤ 2051637692076741^9*6250000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7009677673589724701 6250000000000000000 2051637692076741 2000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2051637692076741/2000000000000000 : ℝ)) (X := (7009677673589724701/6250000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s3_1 : P 1 ≤ ((1 : ℝ)*(X 0 1+X 2 1))+(65986103220093/2683400000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 2 0))+(126216253943519/5366800000000000 : ℝ)*((1 : ℝ)*(X 0 2+X 2 2)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (13417/25000 : ℝ)) (alpha := (65986103220093/2683400000000000 : ℝ)) (beta := (126216253943519/5366800000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow1,s3_corner1a]) (by linarith only [s3_pow1,s3_corner1b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 1 (by
        change ((1 : ℝ)*pair X 1 0) ≤ (13417/25000 : ℝ)*((1 : ℝ)*pair X 1 1)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_1])
    change lpNorm p (pair X 1) ≤ ((1 : ℝ)*pair X 1 1)+(65986103220093/2683400000000000 : ℝ)*((1 : ℝ)*pair X 1 0)+(126216253943519/5366800000000000 : ℝ)*((1 : ℝ)*pair X 1 2) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have s3_pow2 : (51377/100000 : ℝ) ^ (9/2 : ℝ) ≤ (4994124172009392123/100000000000000000000 : ℝ) := by
    have hpowers : (51377/100000 : ℝ)^9 ≤ (4994124172009392123/100000000000000000000 : ℝ)^2 := by
      have hnat : (51377 : ℕ)^9*100000000000000000000^2 ≤ 4994124172009392123^2*100000^9 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51377 100000 4994124172009392123 100000000000000000000 9 2 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (51377/100000 : ℝ)) (X := (4994124172009392123/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s3_corner2a : (104994124172009392123/100000000000000000000 : ℝ) ≤ (10108886775423379/10000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (104994124172009392123/100000000000000000000 : ℝ)^2 ≤ (10108886775423379/10000000000000000 : ℝ)^9 := by
      have hnat : (104994124172009392123 : ℕ)^2*10000000000000000^9 ≤ 10108886775423379^9*100000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        104994124172009392123 100000000000000000000 10108886775423379 10000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10108886775423379/10000000000000000 : ℝ)) (X := (104994124172009392123/100000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have s3_corner2b : (54994124172009392123/50000000000000000000 : ℝ) ≤ (2042763358089237/2000000000000000 : ℝ) ^ (9/2 : ℝ) := by
    have hpowers : (54994124172009392123/50000000000000000000 : ℝ)^2 ≤ (2042763358089237/2000000000000000 : ℝ)^9 := by
      have hnat : (54994124172009392123 : ℕ)^2*2000000000000000^9 ≤ 2042763358089237^9*50000000000000000000^2 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        54994124172009392123 50000000000000000000 2042763358089237 2000000000000000 2 9 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2042763358089237/2000000000000000 : ℝ)) (X := (54994124172009392123/50000000000000000000 : ℝ)) (by norm_num) 9 2 (by norm_num) hpowers
    exact h
  have major_s3_2 : P 2 ≤ ((1 : ℝ)*(X 0 2+X 1 2))+(108886775423379/5137700000000000 : ℝ)*((1 : ℝ)*(X 0 0+X 1 0))+(52465007511403/2568850000000000 : ℝ)*((1 : ℝ)*(X 0 1+X 1 1)) := by
    have hh := chart_majorant (a := (9/2 : ℝ)) (rho := (51377/100000 : ℝ)) (alpha := (108886775423379/5137700000000000 : ℝ)) (beta := (52465007511403/2568850000000000 : ℝ))
      (by linarith only [hpa] : (1 : ℝ) ≤ p) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith only [s3_pow2,s3_corner2a]) (by linarith only [s3_pow2,s3_corner2b])
      X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]] hX 2 (by
        change ((1 : ℝ)*pair X 2 0) ≤ (51377/100000 : ℝ)*((1 : ℝ)*pair X 2 2)
        simp only [pair0,pair1,pair2,Pi.add_apply]
        linarith only [ratio_s2_2])
    change lpNorm p (pair X 2) ≤ ((1 : ℝ)*pair X 2 2)+(108886775423379/5137700000000000 : ℝ)*((1 : ℝ)*pair X 2 0)+(52465007511403/2568850000000000 : ℝ)*((1 : ℝ)*pair X 2 1) at hh
    simpa only [P,pair0,pair1,pair2,Pi.add_apply] using hh
  have sp_s3_0 : ((-1477161521/10000000000 : ℝ)*X 0 0+(5407166697/10000000000 : ℝ)*X 0 1+(5440915607/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s3_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_1 : ((2704163929/5000000000 : ℝ)*X 1 0+(-1487602769/10000000000 : ℝ)*X 1 1+(1086501261/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s3_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_2 : ((2716152413/5000000000 : ℝ)*X 2 0+(678412439/1250000000 : ℝ)*X 2 1+(-146055399/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s3_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_6 : ((2128485407/5000000000 : ℝ)*X 0 0+(1061714023/2500000000 : ℝ)*X 0 1+(2109353733/5000000000 : ℝ)*X 0 2+(2128485407/5000000000 : ℝ)*X 1 0+(1061714023/2500000000 : ℝ)*X 1 1+(2109353733/5000000000 : ℝ)*X 1 2+(2128485407/5000000000 : ℝ)*X 2 0+(1061714023/2500000000 : ℝ)*X 2 1+(2109353733/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s3_s3_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_7 : ((-1332858289/10000000000 : ℝ)*X 0 0+(911641043/2000000000 : ℝ)*X 0 1+(6347237739/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s3_s3_7 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_8 : ((4991378457/10000000000 : ℝ)*X 1 0+(-336755161/5000000000 : ℝ)*X 1 1+(316936581/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s3_s3_8 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_9 : ((2380825951/5000000000 : ℝ)*X 2 0+(6573015857/10000000000 : ℝ)*X 2 1+(-315865357/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s3_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_13 : ((2237311263/5000000000 : ℝ)*X 0 0+(5780068387/10000000000 : ℝ)*X 0 1+(2242354053/10000000000 : ℝ)*X 0 2+(2237311263/5000000000 : ℝ)*X 1 0+(5780068387/10000000000 : ℝ)*X 1 1+(2242354053/10000000000 : ℝ)*X 1 2+(2237311263/5000000000 : ℝ)*X 2 0+(5780068387/10000000000 : ℝ)*X 2 1+(2242354053/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s3_s3_13 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_14 : ((-661783147/10000000000 : ℝ)*X 0 0+(2501043187/5000000000 : ℝ)*X 0 1+(1583737457/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s3_s3_14 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_15 : ((4582799129/10000000000 : ℝ)*X 1 0+(-1330309221/10000000000 : ℝ)*X 1 1+(3163222201/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s3_s3_15 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_16 : ((1265054231/2000000000 : ℝ)*X 2 0+(1255611337/2500000000 : ℝ)*X 2 1+(-644018559/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s3_s3_16 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_20 : ((6329273623/10000000000 : ℝ)*X 0 0+(1920001503/5000000000 : ℝ)*X 0 1+(141942881/625000000 : ℝ)*X 0 2+(6329273623/10000000000 : ℝ)*X 1 0+(1920001503/5000000000 : ℝ)*X 1 1+(141942881/625000000 : ℝ)*X 1 2+(6329273623/10000000000 : ℝ)*X 2 0+(1920001503/5000000000 : ℝ)*X 2 1+(141942881/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s3_s3_20 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_21 : ((-602669483/10000000000 : ℝ)*X 0 0+(5970358569/10000000000 : ℝ)*X 0 1+(1354205887/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s3_s3_21 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_22 : ((6360137219/10000000000 : ℝ)*X 1 0+(-301037737/5000000000 : ℝ)*X 1 1+(2504279759/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s3_s3_22 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_23 : ((4531669757/10000000000 : ℝ)*X 2 0+(6390478873/10000000000 : ℝ)*X 2 1+(-1303130913/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s3_s3_23 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp_s3_27 : ((3252759663/5000000000 : ℝ)*X 0 0+(3071944951/10000000000 : ℝ)*X 0 1+(5620159/19531250 : ℝ)*X 0 2+(3252759663/5000000000 : ℝ)*X 1 0+(3071944951/10000000000 : ℝ)*X 1 1+(5620159/19531250 : ℝ)*X 1 2+(3252759663/5000000000 : ℝ)*X 2 0+(3071944951/10000000000 : ℝ)*X 2 1+(5620159/19531250 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := collision_support_c312063_s3_s3_27 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have ratio_s3_0 : (0 : ℝ) ≤ ((3669/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3669/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (41824608812312371460816808777/4550235704609000000000000000000000 : ℝ) := by norm_num
    linear_combination (1291437/1000000000000 : ℝ)*(base50) + (145923087887/1000000000000 : ℝ)*(base60) + (12816840951/3125000000 : ℝ)*(major_s3_0) + (12816840951/3125000000 : ℝ)*(major_s3_1) + (12816840951/3125000000 : ℝ)*(major_s3_2) + (18585759/1000000000000 : ℝ)*(sp_s3_0) + (11228283/1000000000000 : ℝ)*(sp_s3_6) + (1149104810639/200000000000 : ℝ)*(sp_s3_7) + (5745519851261/1000000000000 : ℝ)*(sp_s3_8) + (287275848421/50000000000 : ℝ)*(sp_s3_9) + (2457190490169/1000000000000 : ℝ)*(sp_s3_13) + (30787311/1000000000000 : ℝ)*(sp_s3_14) + (13393751/250000000000 : ℝ)*(sp_s3_15) + (28228923/500000000000 : ℝ)*(sp_s3_23) + (614300429613/250000000000 : ℝ)*(f.failure) + (2872786713133/500000000000 : ℝ)*(f.sum) + (3558403069592044047/6893252090000000000000000000000 : ℝ)*base63 + (25451297957583/102754000000000000000000000 : ℝ)*base65 + (11138133621483/26834000000000000000000000 : ℝ)*base67 + (87420667995451/102754000000000000000000000 : ℝ)*base69 + (1372336425993421173/3391395770000000000000000000000 : ℝ)*base70 + (9388337612593/13202000000000000000000000 : ℝ)*base73 + (24943862948041/67085000000000000000000000 : ℝ)*base75 + (802738581669/66010000000000000000000000 : ℝ)*base76 + (194183259127792241/885656170000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base80 + (1/1000000000000 : ℝ)*base82 + (5331/25000000000000000 : ℝ)*base86 + (5331/25000000000000000 : ℝ)*base88 + (5331/25000000000000000 : ℝ)*base90 + hcertificate_margin
  have ratio_s3_1 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37237/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(37237/100000 : ℝ)*X 2 1) := by
    have hcertificate_margin : (0 : ℝ) ≤ (979410039212172361131580627131/65003367208700000000000000000000000 : ℝ) := by norm_num
    linear_combination (4362147/1000000000000 : ℝ)*(base60) + (2077261764311/500000000000 : ℝ)*(major_s3_0) + (2077261764311/500000000000 : ℝ)*(major_s3_1) + (2077261764311/500000000000 : ℝ)*(major_s3_2) + (3485579/100000000000 : ℝ)*(sp_s3_0) + (8810657/250000000000 : ℝ)*(sp_s3_1) + (39951491/500000000000 : ℝ)*(sp_s3_2) + (52441861/1000000000000 : ℝ)*(sp_s3_7) + (25836057/500000000000 : ℝ)*(sp_s3_8) + (5819919414267/1000000000000 : ℝ)*(sp_s3_14) + (727489974647/125000000000 : ℝ)*(sp_s3_15) + (1163985361787/200000000000 : ℝ)*(sp_s3_16) + (124446698397/50000000000 : ℝ)*(sp_s3_20) + (50677513/500000000000 : ℝ)*(sp_s3_27) + (1244517661483/500000000000 : ℝ)*(f.failure) + (5820006711917/1000000000000 : ℝ)*(f.sum) + (28278628081210309197/68932520900000000000000000000000 : ℝ)*base63 + (2411588624709899/2568850000000000000000000000 : ℝ)*base64 + (1836468997482811/2683400000000000000000000000 : ℝ)*base66 + (588653733789101/2568850000000000000000000000 : ℝ)*base68 + (33799223424311926173/135655830800000000000000000000000 : ℝ)*base70 + (1781593300492023/2640400000000000000000000000 : ℝ)*base72 + (36877801827087/1341700000000000000000000000 : ℝ)*base74 + (238915227061213/2640400000000000000000000000 : ℝ)*base76 + (1574141865161209413/35426246800000000000000000000000 : ℝ)*base78 + (1/1000000000000 : ℝ)*base81 + (1/1000000000000 : ℝ)*base83 + (11979/50000000000000000 : ℝ)*base87 + (11979/50000000000000000 : ℝ)*base89 + (11979/50000000000000000 : ℝ)*base91 + hcertificate_margin
  have ratio_s3_2 : (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17779/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(17779/50000 : ℝ)*X 1 2) := by
    have hcertificate_margin : (0 : ℝ) ≤ (10051722944784224364384131059143/910047140921800000000000000000000000 : ℝ) := by norm_num
    linear_combination (63589/8000000000 : ℝ)*(base15) + (107886152267/500000000000 : ℝ)*(base40) + (3852935263253/1000000000000 : ℝ)*(major_s3_0) + (3852935263253/1000000000000 : ℝ)*(major_s3_1) + (3852935263253/1000000000000 : ℝ)*(major_s3_2) + (53334443/1000000000000 : ℝ)*(sp_s3_0) + (12834409/250000000000 : ℝ)*(sp_s3_1) + (18110257/500000000000 : ℝ)*(sp_s3_2) + (39274179/1000000000000 : ℝ)*(sp_s3_9) + (33614127/500000000000 : ℝ)*(sp_s3_20) + (5397464092787/1000000000000 : ℝ)*(sp_s3_21) + (5397458140969/1000000000000 : ℝ)*(sp_s3_22) + (674680241567/125000000000 : ℝ)*(sp_s3_23) + (2308282189259/1000000000000 : ℝ)*(sp_s3_27) + (2308349417513/1000000000000 : ℝ)*(f.failure) + (539751742723/100000000000 : ℝ)*(f.sum) + (9392646233894615169/137865041800000000000000000000000 : ℝ)*base62 + (298416357823309/642212500000000000000000000 : ℝ)*base64 + (2535404587679133/5366800000000000000000000000 : ℝ)*base66 + (3403670588665863/5137700000000000000000000000 : ℝ)*base68 + (93779791569293489959/271311661600000000000000000000000 : ℝ)*base70 + (52355544184331/5280800000000000000000000000 : ℝ)*base73 + (100089056050471/2683400000000000000000000000 : ℝ)*base74 + (934282946683159/5280800000000000000000000000 : ℝ)*base76 + (15525732574165944201/70852493600000000000000000000000 : ℝ)*base79 + (1/1000000000000 : ℝ)*base84 + (47369/100000000000000000 : ℝ)*base87 + (47369/100000000000000000 : ℝ)*base89 + (47369/100000000000000000 : ℝ)*base91 + hcertificate_margin
  exact ⟨ratio_s3_0,ratio_s3_1,ratio_s3_2⟩

end HlawkaSchatten.DiagonalCutoff4

theorem solution (p : ℝ) (hpa : (9/2 : ℝ) ≤ p) (hpb : p ≤ (73/16 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : OrderedChart p (166913/100000 : ℝ) (178281/100000 : ℝ) (78337/100000 : ℝ) X ![![0, 1, 2], ![1, 0, 2], ![2, 0, 1]] ![![true, true, true], ![true, true, true], ![true, true, true]])
    (hprev2 : (0 : ℝ) ≤ ((6601/12500 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(6601/12500 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(13417/25000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(13417/25000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(51377/100000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(51377/100000 : ℝ)*X 1 2)) : (0 : ℝ) ≤ ((3669/10000 : ℝ)*X 1 0+(-1 : ℝ)*X 1 1+(3669/10000 : ℝ)*X 2 0+(-1 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(37237/100000 : ℝ)*X 0 1+(-1 : ℝ)*X 2 0+(37237/100000 : ℝ)*X 2 1) ∧ (0 : ℝ) ≤ ((-1 : ℝ)*X 0 0+(17779/50000 : ℝ)*X 0 2+(-1 : ℝ)*X 1 0+(17779/50000 : ℝ)*X 1 2) := by
  exact HlawkaSchatten.DiagonalCutoff4.collision_c312063_s3 p hpa hpb X hX hprev2

#print axioms solution
